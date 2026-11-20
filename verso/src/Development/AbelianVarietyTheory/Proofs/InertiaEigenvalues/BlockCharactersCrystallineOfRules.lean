import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PrimeTypeRows
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationOverSumChar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCyclotomic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

noncomputable section

namespace GlobalTheory.BlockCrys

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke Module TensorProduct

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

/- English proof (translation)
Take `⟨u, hu⟩` from `PD.t_unit`. Set `m : LL ⊗[Qp] B ≃ₗ[LL] LL ⊗[Qp] B` to `AlgebraTensorModule.congr (LinearEquiv.refl LL LL) (u.mulLeftLinearEquiv Qp B)`. Establish `hm : ∀ g y, actVB PD (charRep ψ) g (m y) = m (actVB PD (charRep (ψ * cycLL PD LL)) g y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b`. Establish `h1 : actVB PD (charRep ψ) g (m (v ⊗ₜ b)) = (((ψ g : LLˣ) : LL) * v) ⊗ₜ PD.actB g (PD.t * b)`. Simplify using `[actVB, charRep, m, hu]`. Establish `h2 : m (actVB PD (charRep (ψ * cycLL PD LL)) g (v ⊗ₜ b)) = (((PD.χ g : Qpˣ) : Qp) • (((ψ g : LLˣ) : LL) * v)) ⊗ₜ (PD.t * PD.actB g b)`.

Establish `: ((PD.χ g : Qpˣ) : Qp) • (((ψ g : LLˣ) : LL) * v) = ((ψ g : LLˣ) : LL) * algebraMap Qp LL ((PD.χ g : Qpˣ) : Qp) * v`. Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using `[actVB, charRep, m, hu, cycLL]`.

Rewrite using `[h1, h2, map_mul, PD.t_act, TensorProduct.smul_tmul, smul_mul_assoc]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `h : (Dcris PD (charRep (ψ * cycLL PD LL))).map (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B) = Dcris PD (charRep ψ)`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `m.surjective x`.

Simplify using `only [Submodule.mem_map, LinearEquiv.coe_coe, m.injective.eq_iff, exists_eq_right, CrystallineSubrepresentation.mem_Dcris, hm]`. Unfold `IsCrys`. Rewrite using `[← h, LinearEquiv.finrank_map_eq]`.
-/
theorem isCrys_mul_cyc (ψ : G →* LLˣ) :
    IsCrys PD (charRep (ψ * cycLL PD LL)) ↔ IsCrys PD (charRep ψ) := by
  obtain ⟨u, hu⟩ := PD.t_unit
  let m : LL ⊗[Qp] B ≃ₗ[LL] LL ⊗[Qp] B :=
    AlgebraTensorModule.congr (LinearEquiv.refl LL LL) (u.mulLeftLinearEquiv Qp B)
  have hm : ∀ g y, actVB PD (charRep ψ) g (m y) = m (actVB PD (charRep (ψ * cycLL PD LL)) g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have h1 : actVB PD (charRep ψ) g (m (v ⊗ₜ b)) =
          (((ψ g : LLˣ) : LL) * v) ⊗ₜ PD.actB g (PD.t * b) := by
        simp [actVB, charRep, m, hu]
      have h2 : m (actVB PD (charRep (ψ * cycLL PD LL)) g (v ⊗ₜ b)) =
          (((PD.χ g : Qpˣ) : Qp) • (((ψ g : LLˣ) : LL) * v)) ⊗ₜ (PD.t * PD.actB g b) := by
        have : ((PD.χ g : Qpˣ) : Qp) • (((ψ g : LLˣ) : LL) * v) =
            ((ψ g : LLˣ) : LL) * algebraMap Qp LL ((PD.χ g : Qpˣ) : Qp) * v := by
          rw [Algebra.smul_def]; ring
        rw [this]
        simp [actVB, charRep, m, hu, cycLL]
      rw [h1, h2, map_mul, PD.t_act, TensorProduct.smul_tmul, smul_mul_assoc]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h : (Dcris PD (charRep (ψ * cycLL PD LL))).map (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B) =
      Dcris PD (charRep ψ) := by
    ext x
    obtain ⟨y, rfl⟩ := m.surjective x
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, m.injective.eq_iff, exists_eq_right,
      CrystallineSubrepresentation.mem_Dcris, hm]
  unfold IsCrys
  rw [← h, LinearEquiv.finrank_map_eq]

/- English proof (translation)
Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => rw [zpow_zero, mul_one]`. Consider the case `succ n ih => rw [zpow_add_one, ← mul_assoc, isCrys_mul_cyc, ih]`. Consider the case `pred n ih`. Rewrite using `[← ih, ← isCrys_mul_cyc, mul_assoc, ← zpow_add_one, sub_add_cancel]`.
-/
theorem isCrys_mul_cyc_zpow (ψ : G →* LLˣ) (n : ℤ) :
    IsCrys PD (charRep (ψ * cycLL PD LL ^ n)) ↔ IsCrys PD (charRep ψ) := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, mul_one]
  | succ n ih => rw [zpow_add_one, ← mul_assoc, isCrys_mul_cyc, ih]
  | pred n ih =>
    rw [← ih, ← isCrys_mul_cyc, mul_assoc, ← zpow_add_one, sub_add_cancel]

/- English proof (translation)
Establish `h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL`. Use extensionality with `g`. Simplify using `[charRep]`. Rewrite using `[← one_mul (cycLL PD LL ^ n), isCrys_mul_cyc_zpow, h1]`. Conclude with `GlobalTheory.Survey.CrystallineCyclotomic.isCrys_trivial PD LL`.
-/
theorem isCrys_cyc_zpow [FiniteDimensional Qp LL] (n : ℤ) : IsCrys PD (charRep (cycLL PD LL ^ n)) := by
  have h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL := by
    ext g
    simp [charRep]
  rw [← one_mul (cycLL PD LL ^ n), isCrys_mul_cyc_zpow, h1]
  exact GlobalTheory.Survey.CrystallineCyclotomic.isCrys_trivial PD LL

/- English proof (translation)
Use `hS _ (charRep ψ).dual LL (charRep ψ⁻¹) (LinearMap.mul LL LL) (fun g x => ?_) ?_ (hD LL _ h)` and prove the remaining obligations. Use `ext`. Simplify using `[charRep, Representation.dual_apply, mul_comm, Dual.transpose_apply]`. Introduce `x y hxy`. Simplify using `using LinearMap.congr_fun hxy 1`.
-/
theorem isCrys_inv (hS : CrystallineSubrepresentation.SubCrys PD LL) (hD : CrystallineSubrepresentation.DualCrys PD LL) (ψ : G →* LLˣ)
    (h : IsCrys PD (charRep ψ)) : IsCrys PD (charRep ψ⁻¹) := by
  refine hS _ (charRep ψ).dual LL (charRep ψ⁻¹) (LinearMap.mul LL LL) (fun g x => ?_) ?_ (hD LL _ h)
  · ext
    simp [charRep, Representation.dual_apply, mul_comm, Dual.transpose_apply]
  · intro x y hxy
    simpa using LinearMap.congr_fun hxy 1

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf hi hc`. Establish `hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ g)`. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨ρ' g v, hf g v⟩`. Set `τ` to `ρ.quotient (LinearMap.range f) hst`.

Establish `hτ : ∀ g v, (LinearMap.range f).mkQ (ρ g v) = τ g ((LinearMap.range f).mkQ v)` using `fun g v => rfl`. Take `⟨fA, lA⟩` from `hb V' ρ'`. Take `⟨fQ, lQ⟩` from `hb _ τ`. Take `⟨-, lS⟩` from `GlobalTheory.CrysSub.finrank_le_of_ker_le _ _ (GlobalTheory.CrysSub.exact_Dmap PD ρ' ρ τ f (LinearMap.range f).mkQ hf hτ hi (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective)`. Establish `h3` using `(LinearMap.range f).finrank_quotient_add_finrank`.

Rewrite `h3` using `[LinearMap.finrank_range_of_inj hi]`. Unfold `IsCrys at hc ⊢`. Rewrite `hc` using `[← h3, mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem subCrys_of_bound
    (hb : ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
      [FiniteDimensional LL V] (ρ : Representation LL G V),
      Module.Finite LL (Dcris PD ρ) ∧ finrank LL (Dcris PD ρ) ≤ finrank Qp K₀ * finrank LL V) :
    CrystallineSubrepresentation.SubCrys PD LL := by
  intro V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf hi hc
  have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ' g v, hf g v⟩
  let τ := ρ.quotient (LinearMap.range f) hst
  have hτ : ∀ g v, (LinearMap.range f).mkQ (ρ g v) = τ g ((LinearMap.range f).mkQ v) :=
    fun g v => rfl
  obtain ⟨fA, lA⟩ := hb V' ρ'
  obtain ⟨fQ, lQ⟩ := hb _ τ
  obtain ⟨-, lS⟩ := GlobalTheory.CrysSub.finrank_le_of_ker_le _ _
    (GlobalTheory.CrysSub.exact_Dmap PD ρ' ρ τ f (LinearMap.range f).mkQ hf hτ hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective)
  have h3 := (LinearMap.range f).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hi] at h3
  unfold IsCrys at hc ⊢
  rw [← h3, mul_add] at hc
  omega

end Generic

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `set s : Ω ≃ₐ[E] Ω := ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω) with hs`. Use `set z : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ E Ω l s : ℤ_[l]ˣ) : ℤ_[l]) with hz`. Establish `key : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Introduce `m`.

Establish `: NeZero (l ^ m)` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)`. Establish `hj : IsPrimitiveRoot (Bw.j ζ) (l ^ m)` using `hζ.map_of_injective Bw.j.injective`.

Take `⟨a, ha, hga⟩` from `P.χQ_cyc (g : GQ l) m _ hj.pow_eq_one`. Use `set b := (PadicInt.toZModPow m z).val with hbdef`. Establish `hb : ‖(z : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Establish `: ‖z - (b : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hbdef, ZMod.natCast_zmod_val, sub_self]`.

Rewrite `this` using `[PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast]`. Conclude with `this`. Establish `hsb : s ζ = ζ ^ b` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω s) ζ hζ.pow_eq_one`. Establish `hgb : (g : GQ l) (Bw.j ζ) = Bw.j ζ ^ b`. Establish `h1` using `Bw.e_comm (Bw.e.symm g) ζ`.

Rewrite `h1` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[h1, ← map_pow, ← hsb]`. Both sides reduce to the same expression. Establish `hab : a ≡ b [MOD l ^ m]`. Establish `h0 : Bw.j ζ ^ a = Bw.j ζ ^ b` using `hga.symm.trans hgb`.

Rewrite using `[hj.eq_orderOf]`. Take `⟨u, hu⟩` from `hj.isUnit (NeZero.ne _)`. Rewrite `h0`, the goal using `[← hu]`. Rewrite using `[orderOf_units]`. Conclude with `pow_eq_pow_iff_modEq.mp (Units.ext (by simpa using h0))`.

Establish `hd : ‖(((b : ℤ) - (a : ℤ) : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Rewrite using `[Padic.norm_int_le_pow_iff_dvd]`. Conclude with `hab.dvd` after adjusting the coercions. Move the coercions through the operations in `at hd`. Establish `e : (P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l]) = (((P.χQ (g : GQ l) : ℚ_[l]) - a) + -((b : ℚ_[l]) - a)) + -((z : ℚ_[l]) - b)` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `: ‖(P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l])‖ ≤ 0`.

Establish `ht : Filter.Tendsto (fun m : ℕ => ((l : ℝ)⁻¹) ^ m) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1)`. Use `ge_of_tendsto' ht fun m => ?_` and prove the remaining obligations. Simplify `key m` using `[zpow_neg, zpow_natCast, inv_pow]`. Conclude with `sub_eq_zero.mp (norm_le_zero_iff.mp this)`.
-/
theorem cyc_bridge (g : ↥(GK Bw.Kw)) :
    ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
      (((ReciprocityTheory.Gal.cycZ E Ω l ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  set s : Ω ≃ₐ[E] Ω := ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω) with hs
  set z : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ E Ω l s : ℤ_[l]ˣ) : ℤ_[l]) with hz
  have key : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hj : IsPrimitiveRoot (Bw.j ζ) (l ^ m) := hζ.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) m _ hj.pow_eq_one
    set b := (PadicInt.toZModPow m z).val with hbdef
    have hb : ‖(z : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have : ‖z - (b : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
        rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
          map_natCast, hbdef, ZMod.natCast_zmod_val, sub_self]
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
      exact this
    have hsb : s ζ = ζ ^ b :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω s) ζ hζ.pow_eq_one
    have hgb : (g : GQ l) (Bw.j ζ) = Bw.j ζ ^ b := by
      have h1 := Bw.e_comm (Bw.e.symm g) ζ
      rw [MulEquiv.apply_symm_apply] at h1
      rw [h1, ← map_pow, ← hsb]
      rfl
    have hab : a ≡ b [MOD l ^ m] := by
      have h0 : Bw.j ζ ^ a = Bw.j ζ ^ b := hga.symm.trans hgb
      rw [hj.eq_orderOf]
      obtain ⟨u, hu⟩ := hj.isUnit (NeZero.ne _)
      rw [← hu] at h0 ⊢
      rw [orderOf_units]
      exact pow_eq_pow_iff_modEq.mp (Units.ext (by simpa using h0))
    have hd : ‖(((b : ℤ) - (a : ℤ) : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [Padic.norm_int_le_pow_iff_dvd]
      exact_mod_cast hab.dvd
    push_cast at hd
    have e : (P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]) - a) + -((b : ℚ_[l]) - a)) + -((z : ℚ_[l]) - b) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have : ‖(P.χQ (g : GQ l) : ℚ_[l]) - (z : ℚ_[l])‖ ≤ 0 := by
    have ht : Filter.Tendsto (fun m : ℕ => ((l : ℝ)⁻¹) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1)
    refine ge_of_tendsto' ht fun m => ?_
    simpa [zpow_neg, zpow_natCast, inv_pow] using key m
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

end Bridge

section Regular

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {n : ℕ}

/- English proof (translation)
The claim follows from `((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul c b`.
-/
theorem act_smul (g : G) (c : Qp) (b : B) : PD.actB g (c • b) = c • PD.actB g b :=
  ((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul c b

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply Qp K₀ B, AlgEquiv.commutes]`.
-/
theorem act_algebraMap (g : G) (c : Qp) : PD.actB g (algebraMap Qp B c) = algebraMap Qp B c := by
  rw [IsScalarTower.algebraMap_apply Qp K₀ B, AlgEquiv.commutes]

def coordAct (A : G → Matrix (Fin n) (Fin n) Qp) (g : G) : (Fin n → B) →+ (Fin n → B) where
  toFun x := ((A g).map (algebraMap Qp B)).mulVec fun i => PD.actB g (x i)
  map_zero' := by
    have : (fun i : Fin n => PD.actB g ((0 : Fin n → B) i)) = 0 := funext fun _ => map_zero _
    rw [this, Matrix.mulVec_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    exact map_add _ _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((A g).map (algebraMap Qp B)).mulVec _ = _ • ((A g).map (algebraMap Qp B)).mulVec _`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_mul _ _ _`.
-/
theorem coordAct_smul (A : G → Matrix (Fin n) (Fin n) Qp) (g : G) (b : B) (x : Fin n → B) :
    coordAct PD A g (b • x) = PD.actB g b • coordAct PD A g x := by
  change ((A g).map (algebraMap Qp B)).mulVec _ = _ • ((A g).map (algebraMap Qp B)).mulVec _
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  exact map_mul _ _ _

def coordInv (A : G → Matrix (Fin n) (Fin n) Qp) : Submodule K₀ (Fin n → B) where
  carrier := {x | ∀ g, coordAct PD A g x = x}
  zero_mem' g := map_zero _
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  smul_mem' c x hx g := by
    rw [← algebraMap_smul B c x, coordAct_smul, hx g, AlgEquiv.commutes]

/- English proof (translation)
Set `Φ : V ⊗[Qp] B ≃ₗ[Qp] (Fin n → B)` to `(TensorProduct.comm Qp V B).trans ((Algebra.TensorProduct.basis B e).equivFun.restrictScalars Qp)`. Establish `hΦ : ∀ (v : V) (b : B) i, Φ (v ⊗ₜ b) i = e.repr v i • b`. Introduce `v b i`. Simplify using `[Φ, Algebra.smul_def, mul_comm]`. Establish `hact : ∀ g x, Φ (actVB PD ρ g x) = coordAct PD A g (Φ x)`.

Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Use function extensionality and compare the values at `i`.

Establish `h1 : actVB PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actB g b` using `by simp [actVB]`. Establish `h2 : e.repr (ρ g v) i = ∑ j, A g i j * e.repr v j` using `by conv_lhs => rw [← e.sum_repr v]`. Establish `: ∀ j, ρ g (e.repr v j • e j) = e.repr v j • ρ g (e j)` using `fun j => (ρ g).map_smul_of_tower _ _`. Simplify using `only [map_sum, this, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, hA, mul_comm]`. Rewrite using `[h1, hΦ, h2, Finset.sum_smul]`.

Express the relevant statement in the definitionally equal form `_ = ∑ j, algebraMap Qp B (A g i j) * PD.actB g (Φ (v ⊗ₜ b) j)`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hΦ, act_smul, ← Algebra.smul_def, mul_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hmap : ((Dcris PD ρ).restrictScalars Qp).map (Φ : V ⊗[Qp] B →ₗ[Qp] (Fin n → B)) = (coordInv PD A).restrictScalars Qp`.

Use extensionality with `x`. Take `⟨y, rfl⟩` from `Φ.surjective x`. Simplify using `only [Submodule.mem_map, LinearEquiv.coe_coe, Φ.injective.eq_iff, exists_eq_right, Submodule.restrictScalars_mem, CrystallineSubrepresentation.mem_Dcris]`. Express the relevant statement in the definitionally equal form `_ ↔ ∀ g, coordAct PD A g (Φ y) = Φ y`. Simplify using `only [← hact, Φ.injective.eq_iff]`.

Establish `h3` using `LinearEquiv.finrank_map_eq Φ ((Dcris PD ρ).restrictScalars Qp)`. Rewrite `h3` using `[hmap]`. Rewrite using `[Module.finrank_mul_finrank, Module.finrank_mul_finrank]`. Conclude with `h3.symm`.
-/
theorem finrank_coordInv {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (e : Basis (Fin n) Qp V) (A : G → Matrix (Fin n) (Fin n) Qp)
    (hA : ∀ g i j, A g i j = e.repr (ρ g (e j)) i) :
    finrank Qp LL * finrank LL (Dcris PD ρ) = finrank Qp K₀ * finrank K₀ (coordInv PD A) := by
  let Φ : V ⊗[Qp] B ≃ₗ[Qp] (Fin n → B) :=
    (TensorProduct.comm Qp V B).trans ((Algebra.TensorProduct.basis B e).equivFun.restrictScalars Qp)
  have hΦ : ∀ (v : V) (b : B) i, Φ (v ⊗ₜ b) i = e.repr v i • b := by
    intro v b i
    simp [Φ, Algebra.smul_def, mul_comm]
  have hact : ∀ g x, Φ (actVB PD ρ g x) = coordAct PD A g (Φ x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      funext i
      have h1 : actVB PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actB g b := by simp [actVB]
      have h2 : e.repr (ρ g v) i = ∑ j, A g i j * e.repr v j := by
        conv_lhs => rw [← e.sum_repr v]
        have : ∀ j, ρ g (e.repr v j • e j) = e.repr v j • ρ g (e j) := fun j =>
          (ρ g).map_smul_of_tower _ _
        simp only [map_sum, this, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
          smul_eq_mul, hA, mul_comm]
      rw [h1, hΦ, h2, Finset.sum_smul]
      change _ = ∑ j, algebraMap Qp B (A g i j) * PD.actB g (Φ (v ⊗ₜ b) j)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΦ, act_smul, ← Algebra.smul_def, mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap : ((Dcris PD ρ).restrictScalars Qp).map (Φ : V ⊗[Qp] B →ₗ[Qp] (Fin n → B)) =
      (coordInv PD A).restrictScalars Qp := by
    ext x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, Φ.injective.eq_iff, exists_eq_right,
      Submodule.restrictScalars_mem, CrystallineSubrepresentation.mem_Dcris]
    change _ ↔ ∀ g, coordAct PD A g (Φ y) = Φ y
    simp only [← hact, Φ.injective.eq_iff]
  have h3 := LinearEquiv.finrank_map_eq Φ ((Dcris PD ρ).restrictScalars Qp)
  rw [hmap] at h3
  rw [Module.finrank_mul_finrank, Module.finrank_mul_finrank]
  exact h3.symm

variable [IsDomain B]
  (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * PD.actB g b' = PD.actB g b * b') →
    ∃ c : K₀, b' = algebraMap K₀ B c * b)
  (hunit : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : Qp, PD.actB g b = x • b) → IsUnit b)

include hreg in

/- English proof (translation)
Establish `hr : Module.rank K₀ (coordInv PD A) ≤ n`. Use `rank_le fun s hs => ?_` and prove the remaining obligations. Establish `h1 : LinearIndepOn K₀ (fun x : coordInv PD A => (x : Fin n → B)) s` using `hs.map' (coordInv PD A).subtype (coordInv PD A).ker_subtype`. Establish `h2` using `GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant (fun g b => PD.actB g b) (coordAct PD A) (coordAct_smul PD A) hreg (fun x : coordInv PD A => (x : Fin n → B)) (fun g x => x.2 g) s h1`. Simplify using `using LinearIndependent.fintype_card_le_finrank h2`.

Use `⟨?_, finrank_le_of_rank_le hr⟩` and prove the remaining obligations. Rewrite using `[← Module.rank_lt_aleph0_iff]`. Conclude with `lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0`.
-/
theorem coordInv_le (A : G → Matrix (Fin n) (Fin n) Qp) :
    Module.Finite K₀ (coordInv PD A) ∧ finrank K₀ (coordInv PD A) ≤ n := by
  have hr : Module.rank K₀ (coordInv PD A) ≤ n := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndepOn K₀ (fun x : coordInv PD A => (x : Fin n → B)) s :=
      hs.map' (coordInv PD A).subtype (coordInv PD A).ker_subtype
    have h2 := GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant (fun g b => PD.actB g b) (coordAct PD A)
      (coordAct_smul PD A) hreg (fun x : coordInv PD A => (x : Fin n → B)) (fun g x => x.2 g) s h1
    simpa using LinearIndependent.fintype_card_le_finrank h2
  refine ⟨?_, finrank_le_of_rank_le hr⟩
  rw [← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0

include hreg hunit in

/- English proof (translation)
Use `(coordInv_le PD hreg A).1` as an intermediate fact. Use `(coordInv_le PD hreg A').1` as an intermediate fact. Use `le_antisymm (coordInv_le PD hreg A').2 ?_` and prove the remaining obligations. Set `b` to `Module.finBasisOfFinrankEq K₀ (coordInv PD A) h`. Set `M : Matrix (Fin n) (Fin n) B` to `Matrix.of fun i j => (b j : Fin n → B) i`.

Establish `hind : LinearIndependent B fun j => (b j : Fin n → B)`. Establish `h1 : LinearIndependent K₀ fun j => (b j : Fin n → B)` using `b.linearIndependent.map' (coordInv PD A).subtype (coordInv PD A).ker_subtype`. Establish `h2` using `GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant (fun g b => PD.actB g b) (coordAct PD A) (coordAct_smul PD A) hreg (fun j => (b j : Fin n → B)) (fun g j => (b j).2 g) Finset.univ (h1.linearIndepOn _)`. Rewrite `h2` using `[Finset.coe_univ, linearIndepOn_univ_iff]`. Then use the resulting hypothesis. Establish `hdet : M.det ≠ 0`.

Introduce `h0`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `Fintype.linearIndependent_iff.1 hind v ?_ j` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `congrFun hMv i` as an intermediate fact. Simplify `this` using `[M, Matrix.mulVec, dotProduct, mul_comm]`. Set `a : G → B →+* B` to `fun g => (PD.actB g : B →+* B)`. Set `φ : Qp →+* B` to `algebraMap Qp B`.

Establish `hM : ∀ g, φ.mapMatrix (A g) * (a g).mapMatrix M = M`. Introduce `g`. Use extensionality with `i j`. Conclude with `congrFun ((b j).2 g) i`. Establish `hA2 : ∀ g, (A' g).transpose * A g = 1` using `fun g => mul_eq_one_comm.1 (hA g)`.

Establish `hM2 : ∀ g, (a g).mapMatrix M = φ.mapMatrix (A' g).transpose * M`. Introduce `g`. Use `conv_rhs => rw [← hM g, ← mul_assoc, ← map_mul, hA2, map_one, one_mul]`. Establish `hu : IsUnit M.det`. Use `hunit _ hdet fun g => ⟨(A' g).transpose.det, ?_⟩` and prove the remaining obligations.

Use `congrArg Matrix.det (hM2 g)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]`. Rewrite using `[Algebra.smul_def]`. Conclude with `this`. Establish `hinv : ∀ g, (a g).mapMatrix M⁻¹ * φ.mapMatrix (A' g).transpose = M⁻¹`.

Introduce `g`. Establish `h1 : (a g).mapMatrix M⁻¹ * φ.mapMatrix (A' g).transpose * M = 1`. Rewrite using `[mul_assoc, ← hM2, ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]`. Conclude with `(Matrix.inv_eq_left_inv h1).symm`. Set `d : Fin n → coordInv PD A'` to `fun j => ⟨fun i => M⁻¹ j i, fun g => by`.

Use function extensionality and compare the values at `i`. Rewrite using `[← congrFun (congrFun (hinv g) j) i]`. Express the relevant statement in the definitionally equal form `∑ k, algebraMap Qp B (A' g i k) * PD.actB g (M⁻¹ j k) = ∑ k, PD.actB g (M⁻¹ j k) * algebraMap Qp B (A' g i k)`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _⟩`. Establish `hd : LinearIndependent K₀ d`.

Use `LinearIndependent.of_comp (coordInv PD A').subtype ?_` and prove the remaining obligations. Establish `h1 : LinearIndependent B (M⁻¹).row` using `Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det M).2 hu))`. Conclude with `h1.restrict_scalars (by`. Introduce `x y hxy`. Apply `(algebraMap K₀ B).injective` to reduce the goal to its premises.

Simplify `hxy)` using `[Algebra.smul_def]`. Simplify using `using hd.fintype_card_le_finrank`.
-/
theorem coordInv_dual (A A' : G → Matrix (Fin n) (Fin n) Qp) (hA : ∀ g, A g * (A' g).transpose = 1)
    (h : finrank K₀ (coordInv PD A) = n) : finrank K₀ (coordInv PD A') = n := by
  classical
  have := (coordInv_le PD hreg A).1
  have := (coordInv_le PD hreg A').1
  refine le_antisymm (coordInv_le PD hreg A').2 ?_
  let b := Module.finBasisOfFinrankEq K₀ (coordInv PD A) h
  let M : Matrix (Fin n) (Fin n) B := Matrix.of fun i j => (b j : Fin n → B) i
  have hind : LinearIndependent B fun j => (b j : Fin n → B) := by
    have h1 : LinearIndependent K₀ fun j => (b j : Fin n → B) :=
      b.linearIndependent.map' (coordInv PD A).subtype (coordInv PD A).ker_subtype
    have h2 := GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant (fun g b => PD.actB g b) (coordAct PD A)
      (coordAct_smul PD A) hreg (fun j => (b j : Fin n → B)) (fun g j => (b j).2 g) Finset.univ
      (h1.linearIndepOn _)
    rwa [Finset.coe_univ, linearIndepOn_univ_iff] at h2
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    funext j
    refine Fintype.linearIndependent_iff.1 hind v ?_ j
    funext i
    have := congrFun hMv i
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using this
  let a : G → B →+* B := fun g => (PD.actB g : B →+* B)
  let φ : Qp →+* B := algebraMap Qp B
  have hM : ∀ g, φ.mapMatrix (A g) * (a g).mapMatrix M = M := by
    intro g
    ext i j
    exact congrFun ((b j).2 g) i
  have hA2 : ∀ g, (A' g).transpose * A g = 1 := fun g => mul_eq_one_comm.1 (hA g)
  have hM2 : ∀ g, (a g).mapMatrix M = φ.mapMatrix (A' g).transpose * M := by
    intro g
    conv_rhs => rw [← hM g, ← mul_assoc, ← map_mul, hA2, map_one, one_mul]
  have hu : IsUnit M.det := by
    refine hunit _ hdet fun g => ⟨(A' g).transpose.det, ?_⟩
    have := congrArg Matrix.det (hM2 g)
    rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det] at this
    rw [Algebra.smul_def]
    exact this
  have hinv : ∀ g, (a g).mapMatrix M⁻¹ * φ.mapMatrix (A' g).transpose = M⁻¹ := by
    intro g
    have h1 : (a g).mapMatrix M⁻¹ * φ.mapMatrix (A' g).transpose * M = 1 := by
      rw [mul_assoc, ← hM2, ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    exact (Matrix.inv_eq_left_inv h1).symm
  let d : Fin n → coordInv PD A' := fun j => ⟨fun i => M⁻¹ j i, fun g => by
    funext i
    rw [← congrFun (congrFun (hinv g) j) i]
    change ∑ k, algebraMap Qp B (A' g i k) * PD.actB g (M⁻¹ j k) =
      ∑ k, PD.actB g (M⁻¹ j k) * algebraMap Qp B (A' g i k)
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _⟩
  have hd : LinearIndependent K₀ d := by
    refine LinearIndependent.of_comp (coordInv PD A').subtype ?_
    have h1 : LinearIndependent B (M⁻¹).row :=
      Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_nonsing_inv_iff).2
        ((Matrix.isUnit_iff_isUnit_det M).2 hu))
    exact h1.restrict_scalars (by
      intro x y hxy
      apply (algebraMap K₀ B).injective
      simpa [Algebra.smul_def] using hxy)
  simpa using hd.fintype_card_le_finrank

include hreg hunit in

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ hc`. Establish `: FiniteDimensional Qp V` using `Module.Finite.trans LL V`. Establish `: FiniteDimensional Qp (Dual LL V)` using `Module.Finite.trans LL _`. Use `PD.finK₀` as an intermediate fact. Set `e` to `Module.finBasis Qp V`.

Set `T : Dual LL V →ₗ[Qp] Dual Qp V` to `{ toFun := fun f => (Algebra.trace Qp LL).comp (f.restrictScalars Qp) map_add' := fun f g => by ext; simp map_smul' := fun c f => by ext; simp }`. Establish `hT : Function.Injective T`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f hf`. Use extensionality with `v`.

Use `(traceForm_nondegenerate Qp LL).1 (f v) fun y => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun hf (y • v)` as an intermediate fact. Simplify `this` using `[T, mul_comm]`. Establish `hdim : finrank Qp (Dual LL V) = finrank Qp (Dual Qp V)`. Rewrite using `[← Module.finrank_mul_finrank Qp LL (Dual LL V), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, Module.finrank_mul_finrank]`.

Set `T' : Dual LL V ≃ₗ[Qp] Dual Qp V` to `LinearMap.linearEquivOfInjective T hT hdim`. Set `e' : Basis (Fin (finrank Qp V)) Qp (Dual LL V)` to `e.dualBasis.map T'.symm`. Set `ρQ : G →* Module.End Qp V` to `{ toFun := fun g => (ρ g).restrictScalars Qp map_one' := by ext; simp map_mul' := fun g h => by ext; simp }`. Set `A : G → Matrix (Fin (finrank Qp V)) (Fin (finrank Qp V)) Qp` to `fun g => LinearMap.toMatrix e e (ρQ g)`. Establish `h1` using `finrank_coordInv PD ρ e A fun g i j => LinearMap.toMatrix_apply e e _ i j`.

Establish `h2` using `finrank_coordInv PD ρ.dual e' (fun g => (A g⁻¹).transpose) fun g i j => by`. Establish `h3 : ∀ v, Algebra.trace Qp LL (e' j v) = e.repr v j` using `fun v => by`. Establish `: T (e' j) = e.dualBasis j`. Express the relevant statement in the definitionally equal form `T' (e' j) = _`. Simplify using `[e']`.

Simplify `LinearMap.congr_fun this v` using `[T]`. Establish `h4 : e'.repr (ρ.dual g (e' j)) i = Algebra.trace Qp LL (e' j (ρ g⁻¹ (e i)))`. Simplify using `only [e', Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply, Basis.dualBasis_repr]`. Both sides reduce to the same expression. Rewrite using `[h4, h3, Matrix.transpose_apply]`.

Conclude with `LinearMap.toMatrix_apply e e _ j i`. Establish `hK : 0 < finrank Qp K₀` using `Module.finrank_pos`. Establish `hL : 0 < finrank Qp LL` using `Module.finrank_pos`. Establish `hV : finrank Qp LL * finrank LL V = finrank Qp V` using `Module.finrank_mul_finrank Qp LL V`. Unfold `IsCrys at hc ⊢`.

Establish `h5 : finrank K₀ (coordInv PD A) = finrank Qp V`. Rewrite `h1` using `[hc, mul_left_comm, hV]`. Conclude with `(Nat.eq_of_mul_eq_mul_left hK h1).symm`. Establish `h6` using `coordInv_dual PD hreg hunit A (fun g => (A g⁻¹).transpose) (fun g => by`. Simplify using `only [A, Matrix.transpose_transpose]`.

Rewrite using `[← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]) h5`. Rewrite `h2` using `[h6, ← hV, mul_left_comm]`. Rewrite using `[Subspace.dual_finrank_eq]`. Conclude with `Nat.eq_of_mul_eq_mul_left hL h2`.
-/
theorem dualCrys_of_regular [CharZero Qp] (LL : Type) [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] :
    CrystallineSubrepresentation.DualCrys PD LL := by
  intro V _ _ _ _ _ ρ hc
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (Dual LL V) := Module.Finite.trans LL _
  have := PD.finK₀
  let e := Module.finBasis Qp V
  let T : Dual LL V →ₗ[Qp] Dual Qp V :=
    { toFun := fun f => (Algebra.trace Qp LL).comp (f.restrictScalars Qp)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  have hT : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    ext v
    refine (traceForm_nondegenerate Qp LL).1 (f v) fun y => ?_
    have := LinearMap.congr_fun hf (y • v)
    simpa [T, mul_comm] using this
  have hdim : finrank Qp (Dual LL V) = finrank Qp (Dual Qp V) := by
    rw [← Module.finrank_mul_finrank Qp LL (Dual LL V), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq,
      Module.finrank_mul_finrank]
  let T' : Dual LL V ≃ₗ[Qp] Dual Qp V := LinearMap.linearEquivOfInjective T hT hdim
  let e' : Basis (Fin (finrank Qp V)) Qp (Dual LL V) := e.dualBasis.map T'.symm
  let ρQ : G →* Module.End Qp V :=
    { toFun := fun g => (ρ g).restrictScalars Qp
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  let A : G → Matrix (Fin (finrank Qp V)) (Fin (finrank Qp V)) Qp := fun g => LinearMap.toMatrix e e (ρQ g)
  have h1 := finrank_coordInv PD ρ e A fun g i j => LinearMap.toMatrix_apply e e _ i j
  have h2 := finrank_coordInv PD ρ.dual e' (fun g => (A g⁻¹).transpose) fun g i j => by
    have h3 : ∀ v, Algebra.trace Qp LL (e' j v) = e.repr v j := fun v => by
      have : T (e' j) = e.dualBasis j := by
        change T' (e' j) = _
        simp [e']
      simpa [T] using LinearMap.congr_fun this v
    have h4 : e'.repr (ρ.dual g (e' j)) i = Algebra.trace Qp LL (e' j (ρ g⁻¹ (e i))) := by
      simp only [e', Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply, Basis.dualBasis_repr]
      rfl
    rw [h4, h3, Matrix.transpose_apply]
    exact LinearMap.toMatrix_apply e e _ j i
  have hK : 0 < finrank Qp K₀ := Module.finrank_pos
  have hL : 0 < finrank Qp LL := Module.finrank_pos
  have hV : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank Qp LL V
  unfold IsCrys at hc ⊢
  have h5 : finrank K₀ (coordInv PD A) = finrank Qp V := by
    rw [hc, mul_left_comm, hV] at h1
    exact (Nat.eq_of_mul_eq_mul_left hK h1).symm
  have h6 := coordInv_dual PD hreg hunit A (fun g => (A g⁻¹).transpose) (fun g => by
    simp only [A, Matrix.transpose_transpose]
    rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]) h5
  rw [h6, ← hV, mul_left_comm] at h2
  rw [Subspace.dual_finrank_eq]
  exact Nat.eq_of_mul_eq_mul_left hL h2

end Regular

section Tied

open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T`. Use `⟨fun K LL => subCrys_of_bound _ fun V _ _ _ _ _ ρ => GlobalTheory.Per.FontaineBound.dcris_finite_le hC (h C).1 K LL V ρ, fun K LL => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.Per.FontaineBound.isDomain_cris (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)` as an intermediate fact. Use `LL.2` as an intermediate fact. Use `dualCrys_of_regular (P.PD K) (GlobalTheory.Per.FontaineBound.frac_cris hC (h C).1 K) (fun b hb hg => ?_) _` and prove the remaining obligations.

Establish `hq : ∀ x : ℚ_[l], T.eB (algebraMap ℚ_[l] P.R.B x) = C.qB x` using `fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]`. Both sides reduce to the same expression. Establish `hu` using `(h C).2 K (T.eB b) ((map_ne_zero_iff _ T.eB.injective).2 hb) fun g hg' => by`. Take `⟨x, hx⟩` from `hg ⟨g, hg'⟩`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← T.actB, ← hq, ← map_mul, ← Algebra.smul_def, ← hx, P.PD_actB]`. Simplify using `using hu.map T.eB.symm`.
-/
theorem sub_dual_of_tied (T : LocTied l P AI) (h : ∀ C : GlobalTheory.MemLoc.Core l, C.TensorInj ∧ C.Regular) :
    CrystallineSubrepresentation.LocSubCrys l P ∧ CrystallineSubrepresentation.LocDualCrys l P := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  refine ⟨fun K LL => subCrys_of_bound _ fun V _ _ _ _ _ ρ =>
    GlobalTheory.Per.FontaineBound.dcris_finite_le hC (h C).1 K LL V ρ, fun K LL => ?_⟩
  have := GlobalTheory.Per.FontaineBound.isDomain_cris (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)
  have := LL.2
  refine dualCrys_of_regular (P.PD K) (GlobalTheory.Per.FontaineBound.frac_cris hC (h C).1 K) (fun b hb hg => ?_) _
  have hq : ∀ x : ℚ_[l], T.eB (algebraMap ℚ_[l] P.R.B x) = C.qB x := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
    rfl
  have hu := (h C).2 K (T.eB b) ((map_ne_zero_iff _ T.eB.injective).2 hb) fun g hg' => by
    obtain ⟨x, hx⟩ := hg ⟨g, hg'⟩
    refine ⟨x, ?_⟩
    rw [← T.actB, ← hq, ← map_mul, ← Algebra.smul_def, ← hx, P.PD_actB]
  simpa using hu.map T.eB.symm

end Tied

section Place

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

/- English proof (translation)
The claim follows from `MonoidHom.ext fun _ => map_inv (Units.map (D.nbr i w hw).toLL.toMonoidHom) _`.
-/
theorem locChi_inv (χ : GE D.nd →* (D.nd.O i)ˣ) :
    Br.locChi D.nbr i w hw χ⁻¹ = (Br.locChi D.nbr i w hw χ)⁻¹ :=
  MonoidHom.ext fun _ => map_inv (Units.map (D.nbr i w hw).toLL.toMonoidHom) _

/- English proof (translation)
The claim follows from `MonoidHom.ext fun _ => map_zpow (Units.map (D.nbr i w hw).toLL.toMonoidHom) _ n`.
-/
theorem locChi_zpow (χ : GE D.nd →* (D.nd.O i)ˣ) (n : ℤ) :
    Br.locChi D.nbr i w hw (χ ^ n) = (Br.locChi D.nbr i w hw χ) ^ n :=
  MonoidHom.ext fun _ => map_zpow (Units.map (D.nbr i w hw).toLL.toMonoidHom) _ n

/- English proof (translation)
Use extensionality with `g`. Establish `h1` using `cyc_bridge (D.nbr i w hw) (D.loc (D.nd.l i)) g`. Establish `h2` using `(D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw g`. Establish `h3 : ∀ z : ℤ_[D.nd.l i], (D.nbr i w hw).toLL (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z) = algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (z : ℚ_[D.nd.l i])` using `fun z => by`. Express the relevant statement in the definitionally equal form `algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) ((D.nbr i w hw).eO _) = _`.

Rewrite using `[(D.nbr i w hw).eO_alg]`. Both sides reduce to the same expression. Conclude with `congrArg Subtype.val ((h3 _).trans (congrArg _ (h2.trans h1).symm))`.
-/
theorem locChi_eps :
    Br.locChi D.nbr i w hw (epsU D.nd i) = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) := by
  ext g
  have h1 := cyc_bridge (D.nbr i w hw) (D.loc (D.nd.l i)) g
  have h2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw g
  have h3 : ∀ z : ℤ_[D.nd.l i], (D.nbr i w hw).toLL (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (z : ℚ_[D.nd.l i]) := fun z => by
    change algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) ((D.nbr i w hw).eO _) = _
    rw [(D.nbr i w hw).eO_alg]
    rfl
  exact congrArg Subtype.val ((h3 _).trans (congrArg _ (h2.trans h1).symm))

/- English proof (translation)
Unfold `BlockCharactersCrystallineNonGaloisCusps.CharCrysAt`. Rewrite using `[locChi_zpow, locChi_eps]`. Conclude with `isCrys_cyc_zpow _ n`.
-/
theorem charCrysAt_eps_zpow (n : ℤ) : BlockCharactersCrystallineNonGaloisCusps.CharCrysAt D i w hw (epsU D.nd i ^ n) := by
  unfold BlockCharactersCrystallineNonGaloisCusps.CharCrysAt
  rw [locChi_zpow, locChi_eps]
  exact isCrys_cyc_zpow _ n

/- English proof (translation)
Introduce `c h1 h2` and use `⟨BlockCharactersCrystallineNonGaloisCusps.chiRatio_eq D i c h1 h2, by rw [BlockCharactersCrystallineNonGaloisCusps.chiRatio_eq D i c h1 h2] exact charCrysAt_eps_zpow D i w hw _⟩`.
-/
theorem chiRatioCrysAt : BlockCharactersCrystallineNonGaloisCusps.ChiRatioCrysAt D i w hw := fun c h1 h2 =>
  ⟨BlockCharactersCrystallineNonGaloisCusps.chiRatio_eq D i c h1 h2, by
    rw [BlockCharactersCrystallineNonGaloisCusps.chiRatio_eq D i c h1 h2]
    exact charCrysAt_eps_zpow D i w hw _⟩

/- English proof (translation)
Take `⟨v, hv, hg⟩` from `h`. Set `v' : Fin n → Br.LL D.nbr i w hw` to `fun a => Br.toLLK (D.nbr i w hw) (v a)`. Establish `hv' : v' ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises.

Use function extensionality and compare the values at `a`. Conclude with `(Br.toLLK (D.nbr i w hw)).injective ((congrFun h0 a).trans (map_zero _).symm)`. Establish `key : ∀ g : Br.G D.nbr i w hw, (Br.loc D.nbr i w hw M g).mulVec v' = ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) • v'`. Introduce `g`. Use function extensionality and compare the values at `a`.

Establish `h1` using `congrArg (Br.toLLK (D.nbr i w hw)) (congrFun (hg (decS D.nd w (Br.iota D.nbr i w hw g))) a)`. Establish `h2 : (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).mulVec v a = ∑ b, toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) * v b` using `rfl`. Rewrite `h1` using `[h2, map_sum, Pi.smul_apply, smul_eq_mul, map_mul, WordJumpsCompare.toLLK_toK]`. Simplify using `only [map_mul, WordJumpsCompare.toLLK_toK] at h1`. Rewrite using `[Pi.smul_apply, smul_eq_mul, WordJumpsCompare.locChi_apply]`.

Conclude with `h1`. Use `hS _ (matRep (Br.loc D.nbr i w hw M)) _ _ (LinearMap.toSpanSingleton _ _ v') (fun g c => ?_) (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton _ hv')) hc` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) • c) • v' = (Br.loc D.nbr i w hw M g).mulVec (c • v')`. Rewrite using `[Matrix.mulVec_smul, key, smul_smul, smul_eq_mul, mul_comm]`.
-/
theorem charCrysAt_of_constituent
    (hS : CrystallineSubrepresentation.SubCrys (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) {n : ℕ}
    (χ : GE D.nd →* (D.nd.O i)ˣ) (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i))
    (h : BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i χ M) (hc : BlockCharactersCrystallineNonGaloisCusps.MatCrysAt D i w hw M) :
    BlockCharactersCrystallineNonGaloisCusps.CharCrysAt D i w hw χ := by
  obtain ⟨v, hv, hg⟩ := h
  let v' : Fin n → Br.LL D.nbr i w hw := fun a => Br.toLLK (D.nbr i w hw) (v a)
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    funext a
    exact (Br.toLLK (D.nbr i w hw)).injective ((congrFun h0 a).trans (map_zero _).symm)
  have key : ∀ g : Br.G D.nbr i w hw, (Br.loc D.nbr i w hw M g).mulVec v' =
      ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) • v' := by
    intro g
    funext a
    have h1 := congrArg (Br.toLLK (D.nbr i w hw))
      (congrFun (hg (decS D.nd w (Br.iota D.nbr i w hw g))) a)
    have h2 : (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).mulVec v a =
        ∑ b, toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) * v b := rfl
    rw [h2, map_sum, Pi.smul_apply, smul_eq_mul, map_mul, WordJumpsCompare.toLLK_toK] at h1
    simp only [map_mul, WordJumpsCompare.toLLK_toK] at h1
    rw [Pi.smul_apply, smul_eq_mul, WordJumpsCompare.locChi_apply]
    exact h1
  refine hS _ (matRep (Br.loc D.nbr i w hw M)) _ _ (LinearMap.toSpanSingleton _ _ v') (fun g c => ?_)
    (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton _ hv')) hc
  change (((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) :
    Br.LL D.nbr i w hw) • c) • v' = (Br.loc D.nbr i w hw M g).mulVec (c • v')
  rw [Matrix.mulVec_smul, key, smul_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use `⟨?_, chiRatioCrysAt D i w hw⟩` and prove the remaining obligations. Unfold `BlockCharactersCrystallineNonGaloisCusps.ChiOneInvCrysAt BlockCharactersCrystallineNonGaloisCusps.CharCrysAt`. Rewrite using `[locChi_inv]`. Conclude with `isCrys_inv _ hS hD _ (charCrysAt_of_constituent D i w hw hS _ M h hc)`.
-/
theorem blockCrysAt_of_rules
    (hS : CrystallineSubrepresentation.SubCrys (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw))
    (hD : CrystallineSubrepresentation.DualCrys (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) {n : ℕ}
    (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i))
    (h : BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (chiU D.nd i 1) M) (hc : BlockCharactersCrystallineNonGaloisCusps.MatCrysAt D i w hw M) :
    BlockCharactersCrystallineNonGaloisCusps.BlockCrysAt D i w hw := by
  refine ⟨?_, chiRatioCrysAt D i w hw⟩
  unfold BlockCharactersCrystallineNonGaloisCusps.ChiOneInvCrysAt BlockCharactersCrystallineNonGaloisCusps.CharCrysAt
  rw [locChi_inv]
  exact isCrys_inv _ hS hD _ (charCrysAt_of_constituent D i w hw hS _ M h hc)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem matCrysAt_iff {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i)) :
    BlockCharactersCrystallineNonGaloisCusps.MatCrysAt D i w hw ((Units.coeHom _).comp r) ↔ Br.IsCrysW D.loc D.nbr i w hw r := Iff.rfl

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Set `c : Fin D.R.t` to `⟨0, D.R.t_odd.pos⟩`. Use `⟨e.symm (Pi.single (Sum.inr c) 1), ?_, fun g => ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `congrArg (fun u => e u (Sum.inr c)) h0`.

Simplify using `at h1`. Apply `e.injective` to reduce the goal to its premises. Establish `h2` using `he g (e.symm (Pi.single (Sum.inr c) 1))`. Rewrite using `[map_smul, e.apply_symm_apply]`. Rewrite `h2` using `[e.apply_symm_apply]`.

Use `h2.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((RepresentationOverSumChar.sumChi D.nd i ρ g).map (toK D.nd i)).mulVec _ = _`. Rewrite using `[Matrix.mulVec_single_one]`. Use function extensionality and compare the values at `a`. Break down `a with a | a` into its components or cases.

Simplify using `[RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum]`. Distinguish the cases in `ha : a = c`. Substitute `ha` using the available equality. Simplify using `[RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum, c]`. Simplify using `[RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum, ha]`.
-/
theorem isConstituent_of_splitsAs (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (h : RepresentationOverSumChar.SplitsAs D.nd i r ρ) :
    BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (chiU D.nd i 1) ((Units.coeHom _).comp r) := by
  obtain ⟨e, he⟩ := h
  let c : Fin D.R.t := ⟨0, D.R.t_odd.pos⟩
  refine ⟨e.symm (Pi.single (Sum.inr c) 1), ?_, fun g => ?_⟩
  · intro h0
    have h1 := congrArg (fun u => e u (Sum.inr c)) h0
    simp at h1
  · apply e.injective
    have h2 := he g (e.symm (Pi.single (Sum.inr c) 1))
    rw [map_smul, e.apply_symm_apply]
    rw [e.apply_symm_apply] at h2
    refine h2.trans ?_
    change ((RepresentationOverSumChar.sumChi D.nd i ρ g).map (toK D.nd i)).mulVec _ = _
    rw [Matrix.mulVec_single_one]
    funext a
    rcases a with a | a
    · simp [RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum]
    · by_cases ha : a = c
      · subst ha
        simp [RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum, c]
      · simp [RepresentationOverSumChar.sumChi, RepresentationOverSumChar.blockSum, ha]

end Place

def SubDualRules : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
    CrystallineSubrepresentation.LocSubCrys l P ∧ CrystallineSubrepresentation.LocDualCrys l P

/- English proof (translation)
Introduce `_ _ _ _ ⟨T⟩` and use `sub_dual_of_tied T fun C => ⟨h.tensorInj C, h.regular C⟩`.
-/
theorem subDualRules_of_fontaine (h : GlobalTheory.Published.FontaineBcris) : SubDualRules :=
  fun _ _ _ _ ⟨T⟩ => sub_dual_of_tied T fun C => ⟨h.tensorInj C, h.regular C⟩

/- English proof (translation)
Introduce `D i _ _ _ π _ hχ w hw hc` and use `have hR := h (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩ blockCrysAt_of_rules D i w hw (hR.1 _ _) (hR.2 _ _) _ hχ (hc π)`.
-/
theorem blockCharactersCrystalline_of_rules (h : SubDualRules) : BlockCharactersCrystallineNonGaloisCusps.BlockCharactersCrystalline :=
  fun D i _ _ _ π _ hχ w hw hc =>
    have hR := h (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
    blockCrysAt_of_rules D i w hw (hR.1 _ _) (hR.2 _ _) _ hχ (hc π)

/- English proof (translation)
The claim follows from `blockCharactersCrystalline_of_rules (subDualRules_of_fontaine h)`.
-/
theorem blockCharactersCrystalline (h : GlobalTheory.Published.FontaineBcris) : BlockCharactersCrystallineNonGaloisCusps.BlockCharactersCrystalline :=
  blockCharactersCrystalline_of_rules (subDualRules_of_fontaine h)

def Splitting_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, BlockCharactersCrystallineNonGaloisCusps.NoLevelPrime D i → (∃ a, PrimeTypeWeightPartitions.IsWeight D i a) ∧
    ∀ π ∈ D.nd.Z i, ∃ r ρ, IsHeckeGalois D.nd i π r ∧ RepresentationOverSumChar.SplitsAs D.nd i r ρ

/- English proof (translation)
Introduce and unpack `i hi ⟨π, hπ⟩ w hw`. Take `⟨⟨a, ha⟩, hZ⟩` from `hS i hi`. Take `⟨r, ρ, hr, hρ⟩` from `hZ π hπ`. Establish `hR` using `subDualRules_of_fontaine h (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩`. Conclude with `blockCrysAt_of_rules D i w hw (hR.1 _ _) (hR.2 _ _) _ (isConstituent_of_splitsAs D i r ρ hρ) ((matCrysAt_iff D i w hw r).2 (hG i hi a ha π r hr w hw).1)`.
-/
theorem blockCrys_at_of_rows (h : GlobalTheory.Published.FontaineBcris) (D : D7) (hG : PrimeTypeWeightPartitions.Crys_at D)
    (hS : Splitting_at D) : BlockCharactersCrystallineNonGaloisCusps.BlockCrys_at D := by
  rintro i hi ⟨π, hπ⟩ w hw
  obtain ⟨⟨a, ha⟩, hZ⟩ := hS i hi
  obtain ⟨r, ρ, hr, hρ⟩ := hZ π hπ
  have hR := subDualRules_of_fontaine h (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  exact blockCrysAt_of_rules D i w hw (hR.1 _ _) (hR.2 _ _) _ (isConstituent_of_splitsAs D i r ρ hρ)
    ((matCrysAt_iff D i w hw r).2 (hG i hi a ha π r hr w hw).1)

end GlobalTheory.BlockCrys

import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.JumpsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem UpperTheory.V.Af.NewformAutomorphy.normV_eq UpperTheory.V.Af.NewformAutomorphy.scale_charpoly
  UpperTheory.V.Af.NewformAutomorphy.ss_of_tw from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Take `⟨s0, hs0, hne⟩` from `hne`. Set `M : Γ →* GL (Fin 2) k` to `(MulAut.conj g).toMonoidHom.comp r`. Establish `hM : ∀ s, M s = g * r s * g⁻¹` using `fun _ => rfl`. Establish `h1 : ∀ s ∈ N, M s 1 0 = 0` using `fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)`.

Establish `h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s` using `fun s hs i => (hg ⟨s, hN hs⟩).2 i`. Establish `hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j` using `fun s t i j => by`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `h3 : ∀ d ∈ D, M d 1 0 = 0` using `fun d hd => by`. Establish `e : s0 * d = d * (d⁻¹ * s0 * d)` using `by group`.

Establish `e2` using `hmul s0 d 1 0`. Establish `e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0` using `by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp`. Rewrite `e2` using `[e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3]`. Establish `: (χ 0 s0 : k) - χ 1 s0 ≠ 0` using `sub_ne_zero.2 fun h => hne (Units.ext h)`. Apply `mul_left_cancel₀ this` to reduce the goal to its premises.

Take the linear combination `e2`. Use `⟨fun i => MonoidHom.toHomUnits { toFun := fun s => M s i i map_one' := by simp map_mul' := fun s t => by` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, hmul]`. Use `fin_cases i`. Simplify using `[h3 _ t.2]`.

Simplify using `[h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `absurd hij (by decide)`. Conclude with `absurd hij (by decide)`. Conclude with `h3 _ s.2`.

Conclude with `absurd hij (by decide)`.
-/
private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

/- English proof (translation)
Use `⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring`.
-/
private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `: Matrix.GeneralLinearGroup.det (r s) = Matrix.GeneralLinearGroup.det (g * r s * g⁻¹)`. Rewrite using `[map_mul, map_mul, map_inv, mul_right_comm]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]`. Simplify using the standard rewrite rules.
-/
private theorem det_flag {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ) (κ : Fin 2 → ↥H →* kˣ)
    (h : IsFlagOn r H κ) (s : ↥H) : Matrix.GeneralLinearGroup.det (r s) = κ 0 s * κ 1 s := by
  obtain ⟨g, hg⟩ := h
  have : Matrix.GeneralLinearGroup.det (r s) = Matrix.GeneralLinearGroup.det (g * r s * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
  rw [this]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
  simp

/- English proof (translation)
Use `UpperTheory.V.Af.NewformAutomorphy.ss_of_tw _ χ⁻¹ ?_` and prove the remaining obligations. Use `h` and compare the differences between its conclusion and the goal. Use extensionality with `s : 2`. Rewrite using `[tw_val, tw_val, smul_smul]`. Simplify using the standard rewrite rules.
-/
private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  refine UpperTheory.V.Af.NewformAutomorphy.ss_of_tw _ χ⁻¹ ?_
  convert h
  ext s : 2
  rw [tw_val, tw_val, smul_smul]
  simp

/- English proof (translation)
Take `⟨p1, p2, p3, -⟩` from `UpperTheory.V.Base.places ℚ Ω p A`. Take `⟨v, hv⟩` from `p1 fun h => (p2 h).2 hA`. Establish `hpr : Prime (p : 𝓞 ℚ)`. Establish `e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ)` using `by simp`. Rewrite using `[e]`.

Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)`. Establish `hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal` using `((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)`. Establish `e : v = w` using `HeightOneSpectrum.ext ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))`. Conclude with `e ▸ hv`.
-/
private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

/- English proof (translation)
The claim follows from `(Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)`.
-/
private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

/- English proof (translation)
Establish `hu : IsUnit ((l + 1 : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 (by simp)`. Take `⟨s, hs, he⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit`. Use `⟨s, hs, fun k hk h => ?_⟩` and prove the remaining obligations.

Establish `h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[he, hu.unit_spec, map_natCast, map_natCast]`. Establish `h3` using `congrArg Units.val h`. Rewrite `h3` using `[Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one]`.

Use `hl.out.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

/- English proof (translation)
Establish `: IsGalois ℚ Ω` using `{}`. Use `Subgroup.quotient_finite_of_isOpen H hH` as an intermediate fact. Establish `: H.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `hn : H.normalCore.Normal` using `H.normalCore_normal`. Establish `hH' : IsOpen (H.normalCore : Set (G ℚ Ω))` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))`.

Establish `hk : H.normalCore.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Establish `hpow : ∀ s ∈ Ine (F` using `ℚ) B, s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) B := fun s hs => ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩`. Establish `hle : H.normalCore ⊓ Ine (F` using `ℚ) B ≤ H ⊓ Ine (F := ℚ) B := inf_le_inf_right _ H.normalCore_le`. Establish `halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1))`. Use `(algOfCyc P ℚ Ω l ι).1 _ ?_ fun w hw => ⟨B, place_of hB hw, ((2 : ℕ) : ℤ) - 1, H.normalCore.index, Nat.pos_of_ne_zero hk, fun s hs => ?_⟩` and prove the remaining obligations.

Establish `h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ (((2 : ℕ) : ℤ) - 1)` using `(Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (cont_cycBar ℚ Ω l))`. Conclude with `h1`. Establish `h1` using `det_flag W _ _ hfl ⟨_, hle (hpow s hs)⟩`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, ← map_pow, MonoidHom.comp_apply, h1]`. Express the relevant statement in the definitionally equal form `cycBar ℚ Ω l _ ^ (e : ℤ) * cycBar ℚ Ω l _ ^ (-(e : ℤ)) = 1`.

Rewrite using `[← zpow_add, add_neg_cancel, zpow_zero]`. Take `⟨χ, hχ⟩` from `halg`. Establish `hsd` using `(selfDualR P ℚ Ω l ι 2 (by omega) W π hatt _ χ (dual_det W) hχ).1`. Take `⟨-, wt, HT, -, -, hall⟩` from `exR P ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩`. Establish `hG` using `hall W hW hatt`.

Use `⟨⟨wt, HT, hG⟩, fun v => ?_⟩` and prove the remaining obligations. Take `⟨κ, hκ, hI⟩` from `flag_stable W (Dec (F := ℚ) B) _ _ hle (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d, by simpa using conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hd) hs.2⟩) (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by`. Take `⟨s, hs, h⟩` from `cyc_inf hB`. Use `⟨_, hpow s hs, fun h1 => h (H.normalCore.index * (e + e)) (mul_ne_zero hk (by omega)) ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[MonoidHom.zpow_apply, MonoidHom.zpow_apply, map_pow]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1`. Rewrite using `[pow_mul, pow_add]`. Conclude with `mul_eq_one_iff_eq_inv.2 h1) hfl`. Take `⟨w, hw⟩` from `UpperTheory.V.Af.exists_over ℚ l`. Establish `h` using `place_of hB hw`.

Take `⟨j, L0, hj, hBw⟩` from `GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w B hw h`. Take `⟨Bw, hBj, -⟩` from `hBw L0 le_rfl`. Establish `hInd : Induces Bw` using `fun x => by rw [hBj]; exact hj x`. Establish `hJ` using `(hG.above _ _ (Loc.tiedP l) w B h _ Bw hInd).2.1 (Bw.j.comp (algebraMap ℚ Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl`. Establish `hH2` using `jumpsOpen ![(e : ℤ), -(e : ℤ)] W hW B Bw hInd κ _ hH' hκ hI _ _ hJ`.

Take `⟨μ, hμ, -⟩` from `hreg v`. Establish `hW` using `hG.weights (Bw.j.comp (algebraMap ℚ Ω)) μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v])`. Rewrite `hW` using `[hH2]`. Rewrite `hμ` using `[UpperTheory.V.Af.infOf_of_weights _ μ hW]`. Then use the resulting hypothesis.
-/
private theorem inf_char (P : HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    (∃ wt HT, Published.IsGalRepOfR π ι W wt HT) ∧ ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ s ∈ Ine (F := ℚ) B, s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) B := fun s hs =>
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hle : H.normalCore ⊓ Ine (F := ℚ) B ≤ H ⊓ Ine (F := ℚ) B := inf_le_inf_right _ H.normalCore_le
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    refine (algOfCyc P ℚ Ω l ι).1 _ ?_ fun w hw => ⟨B, place_of hB hw, ((2 : ℕ) : ℤ) - 1, H.normalCore.index,
      Nat.pos_of_ne_zero hk, fun s hs => ?_⟩
    · have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ (((2 : ℕ) : ℤ) - 1) :=
        (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (cont_cycBar ℚ Ω l))
      exact h1
    · have h1 := det_flag W _ _ hfl ⟨_, hle (hpow s hs)⟩
      rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one,
        ← map_pow, MonoidHom.comp_apply, h1]
      change cycBar ℚ Ω l _ ^ (e : ℤ) * cycBar ℚ Ω l _ ^ (-(e : ℤ)) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨χ, hχ⟩ := halg
  have hsd := (selfDualR P ℚ Ω l ι 2 (by omega) W π hatt _ χ (dual_det W) hχ).1
  obtain ⟨-, wt, HT, -, -, hall⟩ := exR P ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩
  have hG := hall W hW hatt
  refine ⟨⟨wt, HT, hG⟩, fun v => ?_⟩
  obtain ⟨κ, hκ, hI⟩ := flag_stable W (Dec (F := ℚ) B) _ _ hle
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d,
      by simpa using conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      obtain ⟨s, hs, h⟩ := cyc_inf hB
      refine ⟨_, hpow s hs, fun h1 => h (H.normalCore.index * (e + e)) (mul_ne_zero hk (by omega)) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, map_pow] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_mul, pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl
  obtain ⟨w, hw⟩ := UpperTheory.V.Af.exists_over ℚ l
  have h := place_of hB hw
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := (hG.above _ _ (Loc.tiedP l) w B h _ Bw hInd).2.1 (Bw.j.comp (algebraMap ℚ Ω)) Bw.Kw (AlgHom.id _ _)
    fun _ => rfl
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] W hW B Bw hInd κ _ hH' hκ hI _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hW := hG.weights (Bw.j.comp (algebraMap ℚ Ω)) μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v])
  rw [hH2] at hW
  rwa [UpperTheory.V.Af.infOf_of_weights _ μ hW] at hμ

/- English proof (translation)
Establish `hc' : φ c ≠ 0` using `by simpa using hc`. Use `UpperTheory.V.Af.NewformAutomorphy.scale_charpoly φ (c • M) c⁻¹ (inv_ne_zero hc) (B.map (φ c * ·)) (by` as an intermediate fact. Rewrite using `[smul_smul, inv_mul_cancel₀ hc, one_smul, h, Multiset.map_map]`. Simplify using `only [Function.comp_def, map_inv₀, inv_mul_cancel_left₀ hc'])`. Rewrite `this` using `[Multiset.map_map]`. Then use the resulting hypothesis.
-/
private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have := UpperTheory.V.Af.NewformAutomorphy.scale_charpoly φ (c • M) c⁻¹ (inv_ne_zero hc) (B.map (φ c * ·)) (by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, h, Multiset.map_map]
    simp only [Function.comp_def, map_inv₀, inv_mul_cancel_left₀ hc'])
  rwa [Multiset.map_map] at this

end GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af GlobalTheory.Ord2.AutNewformCopy in

/- English proof (translation)
Introduce and unpack `P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ B hB H hH hfl`. Take `⟨⟨wt, HT, hG⟩, hinf⟩` from `inf_char P ι he W hW π hreg hatt hB H hH hfl`. Take `⟨f, hf⟩` from `hN (2 * e + 1) (by omega) e π fun v => by`. Use `hinf v using 1` and compare the differences between its conclusion and the goal. Simplify using `only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]`.

Apply the tactic sequence `congr 2 <;> push_cast <;> ring`. Establish `hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B → FrobEig ι W w (algSat 2 (normV w) B)`. Introduce `w hw B hB`. Take `⟨⟨σ, hσ⟩, hiso⟩` from `locCompR P.toClassicalTheorems ℚ 2 π w`. Conclude with `satFrob P.toClassicalTheorems ℚ Ω l ι 2 W hW w hw σ B (((satLoc P.toClassicalTheorems ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB) fun A h rc hrc => hG.away w hw A h rc hrc σ hσ`.

Use `⟨f, ss_tw _ _ hatt.1, ?_⟩` and prove the remaining obligations. Use `filter_upwards [UpperTheory.V.Af.NewformAutomorphy.ev_not_mem l hl.out.ne_zero, UpperTheory.V.Af.NewformAutomorphy.ev_not_mem f.M f.pos.ne'] with w hwl hwM A hA`. Establish `hM : ¬ normV w ∣ f.M`. Introduce and unpack `⟨c, hc⟩`. Apply `hwM` to reduce the goal to its premises.

Rewrite using `[hc, Nat.cast_mul, UpperTheory.V.Af.NewformAutomorphy.normV_eq]`. Conclude with `w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)`. Take `⟨S, hS, hpoly⟩` from `hf w hM`. Take `⟨h1, h2⟩` from `hfrob w hwl S hS A hA`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations.

Establish `h3 : cycZ ℚ Ω l s = 1`. Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]`. Simplify using the standard rewrite rules. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]`. Establish `h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]`. Establish `h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ)`.

Rewrite using `[MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀, map_inv₀, map_natCast, inv_zpow', neg_neg]`. Rewrite using `[tw_val, charpoly_smul _ _ _ (Units.ne_zero _) _ (h2 σ hσ), h4, hpoly]`.
-/
theorem GlobalTheory.Ord2.autNewformOfKnownTheorems :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Published.RepNewform → UpperTheory.V.Pr.AutNewform := by
  rintro P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ B hB H hH hfl
  obtain ⟨⟨wt, HT, hG⟩, hinf⟩ := inf_char P ι he W hW π hreg hatt hB H hH hfl
  obtain ⟨f, hf⟩ := hN (2 * e + 1) (by omega) e π fun v => by
    convert hinf v using 1
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    congr 2 <;> push_cast <;> ring
  have hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι W w (algSat 2 (normV w) B) := by
    intro w hw B hB
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P.toClassicalTheorems ℚ 2 π w
    exact satFrob P.toClassicalTheorems ℚ Ω l ι 2 W hW w hw σ B
      (((satLoc P.toClassicalTheorems ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB) fun A h rc hrc => hG.away w hw A h rc hrc σ hσ
  refine ⟨f, ss_tw _ _ hatt.1, ?_⟩
  filter_upwards [UpperTheory.V.Af.NewformAutomorphy.ev_not_mem l hl.out.ne_zero,
    UpperTheory.V.Af.NewformAutomorphy.ev_not_mem f.M f.pos.ne'] with w hwl hwM A hA
  have hM : ¬ normV w ∣ f.M := by
    rintro ⟨c, hc⟩
    apply hwM
    rw [hc, Nat.cast_mul, UpperTheory.V.Af.NewformAutomorphy.normV_eq]
    exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
  obtain ⟨S, hS, hpoly⟩ := hf w hM
  obtain ⟨h1, h2⟩ := hfrob w hwl S hS A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h3 : cycZ ℚ Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp
    apply Units.ext
    rw [tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]
  · have h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
    have h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
      rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀,
        map_inv₀, map_natCast, inv_zpow', neg_neg]
    rw [tw_val, charpoly_smul _ _ _ (Units.ne_zero _) _ (h2 σ hσ), h4, hpoly]

end

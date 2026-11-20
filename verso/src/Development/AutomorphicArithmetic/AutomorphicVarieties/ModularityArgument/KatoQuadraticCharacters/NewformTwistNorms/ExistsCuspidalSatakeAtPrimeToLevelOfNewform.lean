import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatAtLQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NewformAutAtL

open Polynomial

/- English proof (translation)
Establish `key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W` using `fun W => by`. Prove the components needed by the constructor for the conclusion. Introduce `h g v hv`. Use `W.smul_mem ((χ g : k)⁻¹) (h g v hv)` as an intermediate fact. Rewrite `this` using `[tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Then use the resulting hypothesis.

Introduce `h g v hv`. Rewrite using `[tw_val, Matrix.smul_mulVec]`. Conclude with `W.smul_mem _ (h g v hv)`. Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h W ((key W).2 hW)`.

Conclude with `⟨W', (key W').1 hW', hc⟩`.
-/
private theorem ss_of_tw' {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩

/- English proof (translation)
Establish `h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN` after adjusting the coercions. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_not] at hw`.

Conclude with `Ideal.dvd_span_singleton.2 hw`.
-/
private theorem ev_not_mem' (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
private theorem normV_eq' (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

/- English proof (translation)
Establish `hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p`. Rewrite using `[Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]`. Simplify using the standard rewrite rules. Establish `hd : Ideal.absNorm w.asIdeal ∣ p` using `hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)`. Rewrite using `[normV_eq']`.

Use `((Nat.dvd_prime hp).1 hd).resolve_left ?_` and prove the remaining obligations. Rewrite using `[Ideal.absNorm_eq_one_iff]`. Conclude with `w.isPrime.ne_top`.
-/
private theorem normV_rat' {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [normV_eq']
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

/- English proof (translation)
Establish `hc' : φ c ≠ 0` using `by simpa using hc`. Establish `hcard : B.card = 2`. Establish `h1` using `congrArg natDegree h`. Rewrite `h1` using `[natDegree_map, Matrix.charpoly_natDegree_eq_dim]`. Establish `h2` using `natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))`.

Rewrite `h2` using `[Multiset.map_map]`. Simplify using `only [Function.comp_def, Multiset.card_map] at h2`. Rewrite `h1` using `[h2]`. Simplify using `using h1.symm`. Take `⟨x, y, rfl⟩` from `Multiset.card_eq_two.1 hcard`.

Rewrite `h`, the goal using `[Matrix.charpoly_fin_two]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, …`. Establish `e0` using `congrArg (eval 0) h`. Establish `e1` using `congrArg (eval 1) h`. Simplify using `only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1`.

Establish `hd : φ M.det = x * y`. Apply `mul_left_cancel₀ (pow_ne_zero 2 hc')` to reduce the goal to its premises. Take the linear combination `e0`. Establish `ht : φ M.trace = x + y`. Apply `mul_left_cancel₀ hc'` to reduce the goal to its premises.

Take the linear combination `e0 - e1`. Rewrite using `[hd, ht, C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem scale_charpoly' {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

/- English proof (translation)
Introduce `P e g l hl Ω _ _ _ ι V he hf hlM`. Establish `hk : 2 ≤ 2 * e + 1` using `by omega`. Take `⟨π, hinf, hsat⟩` from `P.newform (2 * e + 1) hk g (e : ℤ)`. Use `⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw' _ _ hf.1, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]`.

Introduce `h`. Establish `h1 : ((2 * e + 1 : ℕ) : ℂ) = 1` using `by linear_combination h`. Establish `h2 : 2 * e + 1 = 1` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Introduce `z hz`.

Simplify using `only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz`. Break down `hz with rfl | rfl` into its components or cases. Conclude with `⟨(e : ℤ), by push_cast; ring⟩`. Conclude with `⟨1 - ((2 * e + 1 : ℕ) : ℤ) + e, by push_cast; ring⟩`. Use `filter_upwards [hf.2, ev_not_mem' l hl.out.ne_zero, ev_not_mem' g.M g.pos.ne'] with w hw hwl hwM`.

Establish `hM : ¬ normV w ∣ g.M`. Introduce and unpack `⟨c, hc⟩`. Apply `hwM` to reduce the goal to its premises. Rewrite using `[hc, Nat.cast_mul, normV_eq']`. Conclude with `w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)`.

Take `⟨B, hB, hpoly⟩` from `hsat w hM`. Use `⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(hw A hA).1 s hs`. Establish `h2 : cycZ ℚ Ω l s = 1`. Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations.

Rewrite using `[cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]`. Simplify using the standard rewrite rules. Establish `h3 : (cycBar ℚ Ω l ^ (-(e : ℤ))) s = 1`. Rewrite using `[MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]`. Apply `Units.ext` to reduce the goal to its premises.

Establish `h4` using `congrArg Units.val h1`. Rewrite `h4` using `[tw_val, h3, Units.val_one, one_smul]`. Then use the resulting hypothesis. Establish `h1` using `(hw A hA).2 σ hσ`. Rewrite `h1` using `[tw_val, ← hpoly]`. Use `scale_charpoly' ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹)) _ ?_` and prove the remaining obligations.

Rewrite using `[h1]`. Establish `h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]`. Establish `h3 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ)`.

Rewrite using `[MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, inv_zpow', neg_neg]`. Rewrite using `[h3]`. Introduce `w hw`. Establish `hn : normV w = l` using `normV_rat' hl.out w hw`. Establish `hM : ¬ normV w ∣ g.M` using `hn ▸ hlM`.

Take `⟨B, hB, hpoly⟩` from `hsat w hM`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Rewrite `hpoly` using `[hn]`. Simplify `hpoly` using `only [zpow_natCast]`.
-/
theorem newformAut_atL : Af.Hypotheses₂ → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  intro P e g l hl Ω _ _ _ ι V he hf hlM
  have hk : 2 ≤ 2 * e + 1 := by omega
  obtain ⟨π, hinf, hsat⟩ := P.newform (2 * e + 1) hk g (e : ℤ)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw' _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : ((2 * e + 1 : ℕ) : ℂ) = 1 := by linear_combination h
    have h2 : 2 * e + 1 = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨(e : ℤ), by push_cast; ring⟩
    · exact ⟨1 - ((2 * e + 1 : ℕ) : ℤ) + e, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem' l hl.out.ne_zero, ev_not_mem' g.M g.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ g.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq']
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ (-(e : ℤ))) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly' ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow', neg_neg]
      rw [h3]
  · intro w hw
    have hn : normV w = l := normV_rat' hl.out w hw
    have hM : ¬ normV w ∣ g.M := hn ▸ hlM
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, ?_⟩
    rw [hn] at hpoly
    simpa only [zpow_natCast] using hpoly

end GlobalTheory.NewformAutAtL

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.NewformAutAtL.newformAut_atL | exact GlobalTheory.NewformAutAtL.newformAut_atL | (intros; apply GlobalTheory.NewformAutAtL.newformAut_atL <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_cuspidal_satake_at_prime_to_level_of_newform : Af.Hypotheses₂ → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  first | exact @GlobalTheory.NewformAutAtL.newformAut_atL | exact GlobalTheory.NewformAutAtL.newformAut_atL | (intros; apply GlobalTheory.NewformAutAtL.newformAut_atL <;> assumption)

end

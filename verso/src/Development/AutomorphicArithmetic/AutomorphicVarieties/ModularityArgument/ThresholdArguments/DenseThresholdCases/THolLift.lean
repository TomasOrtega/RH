import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolFin

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
variable {F : Type} [Field F] [NumberField F]
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [HChar.val, HChar.locK, HChar.loc]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]`.
-/
private theorem val_pow (ω : HChar F) (w : Pl F) (n : ℕ) : (ω ^ n).val w = ω.val w ^ n := by
  induction n with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
/- English proof (translation)
Take `⟨n, hn, h⟩` from `isOfFinOrder_iff_pow_eq_one.1 hω`. Use `finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_` and prove the remaining obligations. Introduce `x y hx hy`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ hx (norm_nonneg _) hy`.

Introduce `w`. Rewrite using `[map_pow, norm_pow]`. Use `pow_le_one₀ (norm_nonneg _) ?_` and prove the remaining obligations. Use `split_ifs`. Establish `h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1`.

Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]`. Simplify using the standard rewrite rules. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_pow, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le`.

Simplify using the standard rewrite rules.
-/
private theorem norm_chiI {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (hω : IsOfFinOrder ω) (c : Pl F → ℕ)
    (I : Ideal (𝓞 F)) : ‖ι.symm (chiI ω c I)‖ ≤ 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  refine finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro w
    rw [map_pow, norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs
    · have h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]; simp
      have h2 := congrArg norm h1
      rw [norm_pow, norm_one] at h2
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le
    · simp
private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}
open Classical in
private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring
open Classical in
omit [NumberField F] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl
variable [IsTotallyReal F]
private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩
private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose
/- English proof (translation)
Assemble the required witnesses or components as `⟨_, φ.2.2.choose_spec.choose_spec⟩`.
-/
private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩
/- English proof (translation)
Take `⟨d, hd⟩` from `cf_spec φ`. Conclude with `(expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2`.
-/
private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2
private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp
/- English proof (translation)
The claim follows from `congrArg ι.symm (cf_eq φ h 𝔪)`.
-/
private theorem Phi_eq {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) : Phi ι k c ω φ 𝔪 = ι.symm (a 𝔪.1) := congrArg ι.symm (cf_eq φ h 𝔪)
/- English proof (translation)
Rewrite using `[fT_apply, Phi_eq ι φ h, hkCoef, map_add, map_mul ι.symm _ (coefDiv _ _ _), coefDiv]`. Use `split_ifs with hd`. Rewrite using `[Phi_eq ι φ h]`. Rewrite using `[map_zero]`.
-/
private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (w : Pl F) (𝔪 : Idx F) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) 𝔪 = ι.symm (hkCoef k c ω w a 𝔪.1) := by
  rw [fT_apply, Phi_eq ι φ h, hkCoef, map_add, map_mul ι.symm _ (coefDiv _ _ _), coefDiv]
  split_ifs with hd
  · rw [Phi_eq ι φ h]
  · rw [map_zero]
private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩
/- English proof (translation)
Use function extensionality and compare the values at `𝔪`. Take `⟨_, h⟩` from `cf_spec φ`. Take `⟨d, hd⟩` from `(holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h`. Rewrite using `[fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]`.
-/
private theorem Phi_hkS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) = Phi ι k c ω (hkS hk1 c hω w φ) := by
  funext 𝔪
  obtain ⟨_, h⟩ := cf_spec φ
  obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
  rw [fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]
/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `φ h0`. Take `⟨_, h⟩` from `cf_spec φ`. Use `Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)` and prove the remaining obligations. Use `congrFun h0 ⟨𝔪, h𝔪⟩` as an intermediate fact.

Rewrite `this` using `[Phi_eq ι φ h]`. Simplify using `using this`.
-/
private theorem Phi_inj {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) : Function.Injective (Phi ι k c ω) := by
  rw [injective_iff_map_eq_zero]
  intro φ h0
  obtain ⟨_, h⟩ := cf_spec φ
  refine Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)
  have := congrFun h0 ⟨𝔪, h𝔪⟩
  rw [Phi_eq ι φ h] at this
  simpa using this
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
/- English proof (translation)
Introduce `hP F _ _ _ l _ ι k hk1 c hc ω hω φ c₀ a t hφ hexp hint h1 ht hcong`. Use `haveI : RingHomSurjective (ι.symm : ℂ →+* Qbar l) := ⟨ι.symm.surjective⟩`. Use `haveI := _root_.UpperTheory.V.Sd.holomorphic_finite_of_printed_hida hP F k c hc ω hω`. Use `haveI : FiniteDimensional ℂ (SS k c ω) := Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ}) fun ψ hψ => Submodule.subset_span hψ.1`. Use `set V : Submodule (Qbar l) (Idx F → Qbar l) := (⊤ : Submodule ℂ (SS k c ω)).map (Phi ι k c ω) with hV`.

Establish `hfd : FiniteDimensional (Qbar l) V` using `Module.Finite.iff_fg.2 (Submodule.FG.map _ (IsNoetherian.noetherian _))`. Set `e : Pl F → Qbar l` to `fun w => ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))`. Establish `he : ∀ p, ‖e p‖ ≤ 1`. Introduce `p`. Simplify using `only [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ (norm_chiI ι ω hω c _) (by positivity) (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))`. Establish `hmem : ∀ p : Pl F, ∀ v ∈ V, fT p (e p) v ∈ V`. Introduce and unpack `p _ ⟨g, -, rfl⟩`. Conclude with `⟨hkS hk1 c hω p g, trivial, (Phi_hkS ι hk1 c hω p g).symm⟩`. Set `T : Pl F → Module.End (Qbar l) V` to `fun p => (fT p (e p)).restrict (hmem p)`.

Establish `hT : ∀ p (v : V), (T p v).1 = fT p (e p) v.1` using `fun _ _ => rfl`. Set `f : SS k c ω` to `⟨φ, hφ, _, _, hexp⟩`. Take `⟨h, b, hne, -, heig, hb⟩` from `delSerre l (Idx F) (Pl F) V hfd T (by`. Introduce `p q`. Use `ext1 v`.

Apply `Subtype.ext` to reduce the goal to its premises. Take `⟨_, g, -, rfl⟩` from `v`. Simplify using `only [Module.End.mul_apply, hT, e, Phi_hkS ι hk1 c hω]`. Conclude with `congrArg _ (Subtype.ext ((holHk F k hk1 c ω hω g.1 g.2.1 p).2.1 q)))`. Use the proof step `(by`.

Introduce `p v hv n`. Rewrite using `[hT, fT_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_one₀ (he p) (norm_nonneg _) ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hv _`. Use the proof step `simp)`. Use the proof step `(by`. Introduce `p v hv n`.

Rewrite using `[hT, fT_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hv _) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (he p)).trans_lt ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `hv _`. Use the proof step `simp)`. Use the proof step `⟨Phi ι k c ω f, f, trivial, rfl⟩ (fun p => ι.symm (t p))`. Use the proof step `(by`. Introduce `n`.

Use `show ‖Phi ι k c ω f n‖ ≤ 1`. Rewrite using `[Phi_eq ι f hexp]`. Conclude with `hint _ n.2)`. Use the proof step `⟨⟨⊤, top_ne_bot⟩, by show ‖Phi ι k c ω f _‖ = 1`. Rewrite using `[Phi_eq ι f hexp]`.

Conclude with `h1⟩`. Use `ht`. Use the proof step `(by`. Introduce `p n`. Rewrite using `[hT]`.

Use `show ‖fT p (e p) (Phi ι k c ω f) n - ι.symm (t p) * Phi ι k c ω f n‖ < 1`. Rewrite using `[fT_Phi ι f hexp, Phi_eq ι f hexp, ← map_mul, ← map_sub]`. Conclude with `hcong p _ n.2)`. Take `⟨_, g, hg, rfl⟩` from `h`. Use `⟨g.1, fun w => ι (b w), ⟨g.2.1, fun h0 => hne ?_, fun w => ?_⟩, fun w => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext show Phi ι k c ω g = 0` to reduce the goal to its premises. Rewrite using `[show g = 0 from Subtype.ext h0, map_zero]`. Establish `h2 : fT w (e w) (Phi ι k c ω g) = b w • Phi ι k c ω g` using `congrArg Subtype.val (heig w)`. Establish `h3 : hkS hk1 c hω w g = ι (b w) • g`. Apply `Phi_inj ι hk1 c hω` to reduce the goal to its premises.

Rewrite using `[← Phi_hkS, LinearMap.map_smulₛₗ]`. Use `h2.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `congrArg Subtype.val h3`. Rewrite using `[map_sub, RingEquiv.symm_apply_apply]`.

Conclude with `hb w`.
-/
theorem UpperTheory.V.Sd.holLift_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolLift := by
  intro hP F _ _ _ l _ ι k hk1 c hc ω hω φ c₀ a t hφ hexp hint h1 ht hcong
  haveI : RingHomSurjective (ι.symm : ℂ →+* Qbar l) := ⟨ι.symm.surjective⟩
  haveI := _root_.UpperTheory.V.Sd.holomorphic_finite_of_printed_hida hP F k c hc ω hω
  haveI : FiniteDimensional ℂ (SS k c ω) :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})
      fun ψ hψ => Submodule.subset_span hψ.1
  set V : Submodule (Qbar l) (Idx F → Qbar l) := (⊤ : Submodule ℂ (SS k c ω)).map (Phi ι k c ω) with hV
  have hfd : FiniteDimensional (Qbar l) V :=
    Module.Finite.iff_fg.2 (Submodule.FG.map _ (IsNoetherian.noetherian _))
  let e : Pl F → Qbar l := fun w => ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))
  have he : ∀ p, ‖e p‖ ≤ 1 := by
    intro p
    simp only [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chiI ι ω hω c _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
  have hmem : ∀ p : Pl F, ∀ v ∈ V, fT p (e p) v ∈ V := by
    rintro p _ ⟨g, -, rfl⟩
    exact ⟨hkS hk1 c hω p g, trivial, (Phi_hkS ι hk1 c hω p g).symm⟩
  let T : Pl F → Module.End (Qbar l) V := fun p => (fT p (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p (e p) v.1 := fun _ _ => rfl
  let f : SS k c ω := ⟨φ, hφ, _, _, hexp⟩
  obtain ⟨h, b, hne, -, heig, hb⟩ := delSerre l (Idx F) (Pl F) V hfd T
    (by
      intro p q
      ext1 v
      apply Subtype.ext
      obtain ⟨_, g, -, rfl⟩ := v
      simp only [Module.End.mul_apply, hT, e, Phi_hkS ι hk1 c hω]
      exact congrArg _ (Subtype.ext ((holHk F k hk1 c ω hω g.1 g.2.1 p).2.1 q)))
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)
      rw [norm_mul]
      refine mul_le_one₀ (he p) (norm_nonneg _) ?_
      split_ifs
      · exact hv _
      · simp)
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hv _) ?_)
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (he p)).trans_lt ?_
      split_ifs
      · exact hv _
      · simp)
    ⟨Phi ι k c ω f, f, trivial, rfl⟩ (fun p => ι.symm (t p))
    (by
      intro n
      show ‖Phi ι k c ω f n‖ ≤ 1
      rw [Phi_eq ι f hexp]
      exact hint _ n.2)
    ⟨⟨⊤, top_ne_bot⟩, by
      show ‖Phi ι k c ω f _‖ = 1
      rw [Phi_eq ι f hexp]; exact h1⟩
    ht
    (by
      intro p n
      rw [hT]
      show ‖fT p (e p) (Phi ι k c ω f) n - ι.symm (t p) * Phi ι k c ω f n‖ < 1
      rw [fT_Phi ι f hexp, Phi_eq ι f hexp, ← map_mul, ← map_sub]
      exact hcong p _ n.2)
  obtain ⟨_, g, hg, rfl⟩ := h
  refine ⟨g.1, fun w => ι (b w), ⟨g.2.1, fun h0 => hne ?_, fun w => ?_⟩, fun w => ?_⟩
  · apply Subtype.ext
    show Phi ι k c ω g = 0
    rw [show g = 0 from Subtype.ext h0, map_zero]
  · have h2 : fT w (e w) (Phi ι k c ω g) = b w • Phi ι k c ω g := congrArg Subtype.val (heig w)
    have h3 : hkS hk1 c hω w g = ι (b w) • g := by
      apply Phi_inj ι hk1 c hω
      rw [← Phi_hkS, LinearMap.map_smulₛₗ]
      refine h2.trans ?_
      simp
    exact congrArg Subtype.val h3
  · rw [map_sub, RingEquiv.symm_apply_apply]
    exact hb w
end
end

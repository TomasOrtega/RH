import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ConductorAtMapInjectiveCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountS

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Transfer
variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')
private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f
/- English proof (translation)
The claim follows from `MulChar.injective_ringHomComp hf`.
-/
private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf
/- English proof (translation)
The claim follows from `orderOf_injective _ (chHom_inj f hf) _`.
-/
private theorem chHom_ord (hf : Function.Injective f) (χ : DirichletCharacter O N) : orderOf (chHom f χ) = orderOf χ :=
  orderOf_injective _ (chHom_inj f hf) _
/- English proof (translation)
Use `MulChar.ext fun a => ?_` and prove the remaining obligations. Use `show f (comp r χ a) = _`. Simplify using `only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]`. Both sides reduce to the same expression.
-/
private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl
/- English proof (translation)
Simplify using `only [th0, lPrime, lPart, map_mul, map_inv, map_pow, chHom_ord f hf]`.
-/
private theorem map_injective_coeff_twist_comm (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (th0 l χ) = th0 l (chHom f χ) := by
  simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, chHom_ord f hf]
/- English proof (translation)
Simplify using `only [chiP, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]`.
-/
private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  simp only [chiP, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
/- English proof (translation)
Establish `h : chHom f (th1 l χ) = th1 l (chHom f χ)`. Simplify using `only [th1, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]`. Unfold `n0 f0`. Rewrite using `[← h, chHom_ord f hf]`.
-/
private theorem conductor_at_map_injective_coeff (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    n0 l (chHom f χ) = n0 l χ := by
  have h : chHom f (th1 l χ) = th1 l (chHom f χ) := by
    simp only [th1, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
  unfold n0 f0
  rw [← h, chHom_ord f hf]
/- English proof (translation)
Use extensionality with `u`. Simplify using `only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Conclude with `map_eq_one_iff f hf`.
-/
private theorem chHom_ker (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    (chHom f χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  exact map_eq_one_iff f hf
/- English proof (translation)
Establish `h : ∀ φ : DirichletCharacter O N, (chHom f φ).conductor = φ.conductor` using `fun φ => by`. Unfold `DirichletCharacter.conductor`. Use `congr 1`. Use extensionality with `d`. Simplify using `only [DirichletCharacter.mem_conductorSet_iff]`.

Distinguish the cases in `hd : d ∣ N`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, chHom_ker f hf]`. Conclude with `⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩`. Unfold `c2 psi2`. Rewrite using `[← chHom_comp, h]`.
-/
private theorem parity_at_map_injective_coeff [NeZero N] (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    c2 (chHom f χ) = c2 χ := by
  have h : ∀ φ : DirichletCharacter O N, (chHom f φ).conductor = φ.conductor := fun φ => by
    unfold DirichletCharacter.conductor
    congr 1
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    by_cases hd : d ∣ N
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        chHom_ker f hf]
    · exact ⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩
  unfold c2 psi2
  rw [← chHom_comp, h]
/- English proof (translation)
Use `show f (χ (-1)) = _ ↔ χ (-1) = _`. Rewrite using `[← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]`.
-/
private theorem chHom_even (hf : Function.Injective f) (e : ℕ) (χ : DirichletCharacter O N) :
    PsiEven e (chHom f χ) ↔ PsiEven e χ := by
  show f (χ (-1)) = _ ↔ χ (-1) = _
  rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]
end Transfer
/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot c.O n`. Conclude with `⟨⟨_, hζ.map_of_injective (f := Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)⟩, inferInstance⟩`.
-/
private theorem enough_of_le {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity c.O n] : HasEnoughRootsOfUnity c'.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c.O n
  exact ⟨⟨_, hζ.map_of_injective (f := Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)⟩, inferInstance⟩
/- English proof (translation)
Take `⟨C, A, hc⟩` from `_root_.UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound hN`. Take `⟨C', hC'⟩` from `arith χ C A`. Use `⟨C', fun h hχ t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase r1 r2 => ?_⟩` and prove the remaining obligations. Take `⟨D, hD, hOf⟩` from `dataEx hX Ω h t ht l c e hl2 he0 het ψ hψ hcase r1 r2`. Take `⟨hF, hNE, ι, hAU⟩` from `hA Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf`.

Establish `hctx : Ctx2 D ∨ Ctx3 D` using `hOf.imp (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩) (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)`. Establish `hsha` using `shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf`. Take `⟨M⟩` from `exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)`. Establish `ho : 0 < h.o` using `(hostIndex h).2.2.2.1`. Establish `hlp` using `hl.out`.

Choose the witnesses or unpack the hypotheses as in `⟨n', p₁, m₀, hO, hn', hm₀, har⟩ : ∃ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ ∧ c2 ψ ≤ n' ∧ m₀ ∣ h.o ∧ ((n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ)) := by`. Break down `hOf with ⟨-, hO⟩ | ⟨h3, hO⟩` into its components or cases. Use `⟨_, _, _, hO, ?_, one_dvd _, Or.inl ⟨rfl, rfl⟩⟩` and prove the remaining obligations. Establish `h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2)`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations.

Establish `hq : 0 < h.q` using `NeZero.pos _`. Use `hlp.pos` as an intermediate fact. Rewrite using `[pow_add, mul_assoc, mul_assoc, mul_assoc]`. Conclude with `Nat.le_mul_of_pos_right _ (by positivity)`. Establish `h2` using `Nat.clog_mono_right 2 h1`.

Rewrite `h2` using `[Nat.clog_pow 2 _ (by norm_num)]`. Then use the resulting hypothesis. Take `⟨a, -, b, -⟩` from `(hostOdd h c.O ψ (h.mem_X.1 hψ).1).1 h3.2.2.1`. Conclude with `⟨_, _, _, hO, b ▸ Nat.zero_le _, a.trans (Nat.ordCompl_dvd _ _), Or.inr ⟨rfl, by rw [hχ]⟩⟩`. Take `⟨⟨k1, k2, k3⟩, o1, o2, o3⟩` from `levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ m₀ hO hn' hm₀`. Establish `hp₁ : 0 < p₁`.

Take `⟨a, -⟩` from `hO.xi`. Conclude with `NeZero.pos _`. Establish `hNp` using `h.N_pos`. Establish `hlpos` using `hlp.pos`. Take `⟨q1, q2, q3, -⟩` from `pZeroLe (l * h.N * p₁) (by positivity)`.

Establish `q4 : ¬ pZero (l * h.N * p₁) ∣ 2` using `fun hd => by have := Nat.le_of_dvd two_pos hd; omega`. Establish `q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁` using `fun hd => by`. Rewrite `hd` using `[show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring]`. Conclude with `((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3`. Establish `q6 : pZero (l * h.N * p₁) ∉ D.S` using `fun hd => by`.

Rewrite `hd` using `[hO.S_eq]`. Establish `hd` using `Nat.dvd_of_mem_primeFactors hd`. Rewrite `hd` using `[show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring]`. Conclude with `((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3`. Establish `hlev : 1 ≤ l * 2 ^ n' * h.N * p₁` using `Nat.pos_of_ne_zero (by positivity)`.

Establish `hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o)`. Establish `: 0 < l - 1` using `Nat.sub_pos_of_lt hlp.one_lt`. Check the signs of the components of the expression. Take `⟨σ, hσ, hle⟩` from `hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU`. Establish `hI : D.Ineq σ` using `galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE (fun r hr hi => hAd Ω l c D hctx _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ`.

Establish `he2 : 2 ≤ e` using `hO.e_eq ▸ hD.two_le`. Establish `hb` using `hC' h hχ l c e hl2 he2 ψ hψ n' p₁ har`. Establish `hle'` using `hle hI`. Rewrite `hle'` using `[hO.e_eq]`. Use `⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)`.
-/
private theorem main_big (hA : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) (hP : CohomologyHyp) (hM : LemmaM) (hM' : LemmaM') (hLP : LemmaP) (hN : _root_.UpperTheory.V.Af.NumberSp4Alt)
    (hAd : _root_.UpperTheory.V.Th.RigiditySymplecticFour) (hX : X.CorX)
    (hSo : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l)
    (χ : Formalism.HC.PChar) : ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ ∨ h.CaseIII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) → HasEnoughRootsOfUnity c.O (2 ^ h.nIII l ψ) →
      VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C) := by
  obtain ⟨C, A, hc⟩ := _root_.UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound hN
  obtain ⟨C', hC'⟩ := arith χ C A
  refine ⟨C', fun h hχ t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase r1 r2 => ?_⟩
  obtain ⟨D, hD, hOf⟩ := dataEx hX Ω h t ht l c e hl2 he0 het ψ hψ hcase r1 r2
  obtain ⟨hF, hNE, ι, hAU⟩ := hA Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  have hctx : Ctx2 D ∨ Ctx3 D :=
    hOf.imp (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
      (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
  have hsha := shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  obtain ⟨M⟩ := exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)
  have ho : 0 < h.o := (hostIndex h).2.2.2.1
  have hlp := hl.out
  obtain ⟨n', p₁, m₀, hO, hn', hm₀, har⟩ : ∃ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ ∧ c2 ψ ≤ n' ∧ m₀ ∣ h.o ∧
      ((n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ)) := by
    rcases hOf with ⟨-, hO⟩ | ⟨h3, hO⟩
    · refine ⟨_, _, _, hO, ?_, one_dvd _, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2) := by
        refine le_trans ?_ (le_max_right _ _)
        have hq : 0 < h.q := NeZero.pos _
        have := hlp.pos
        rw [pow_add, mul_assoc, mul_assoc, mul_assoc]
        exact Nat.le_mul_of_pos_right _ (by positivity)
      have h2 := Nat.clog_mono_right 2 h1
      rwa [Nat.clog_pow 2 _ (by norm_num)] at h2
    · obtain ⟨a, -, b, -⟩ := (hostOdd h c.O ψ (h.mem_X.1 hψ).1).1 h3.2.2.1
      exact ⟨_, _, _, hO, b ▸ Nat.zero_le _, a.trans (Nat.ordCompl_dvd _ _), Or.inr ⟨rfl, by rw [hχ]⟩⟩
  obtain ⟨⟨k1, k2, k3⟩, o1, o2, o3⟩ := levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ m₀ hO hn' hm₀
  have hp₁ : 0 < p₁ := by
    obtain ⟨a, -⟩ := hO.xi
    exact NeZero.pos _
  have hNp := h.N_pos
  have hlpos := hlp.pos
  obtain ⟨q1, q2, q3, -⟩ := pZeroLe (l * h.N * p₁) (by positivity)
  have q4 : ¬ pZero (l * h.N * p₁) ∣ 2 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  have q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁ := fun hd => by
    rw [show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3
  have q6 : pZero (l * h.N * p₁) ∉ D.S := fun hd => by
    rw [hO.S_eq] at hd
    have hd := Nat.dvd_of_mem_primeFactors hd
    rw [show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3
  have hlev : 1 ≤ l * 2 ^ n' * h.N * p₁ := Nat.pos_of_ne_zero (by positivity)
  have hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o) := by
    have : 0 < l - 1 := Nat.sub_pos_of_lt hlp.one_lt
    positivity
  obtain ⟨σ, hσ, hle⟩ := hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU
  have hI : D.Ineq σ := galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE
    (fun r hr hi => hAd Ω l c D hctx _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ
  have he2 : 2 ≤ e := hO.e_eq ▸ hD.two_le
  have hb := hC' h hχ l c e hl2 he2 ψ hψ n' p₁ har
  have hle' := hle hI
  rw [hO.e_eq] at hle'
  refine ⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩
  exact mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)
/- English proof (translation)
Introduce `hA hP hM hM' hLP hN hAd hX hSo`. Establish `key : CountShape fun h l _ _ e ψ => h.CaseII l e ψ ∨ h.CaseIII l e ψ`. Introduce `χ`. Take `⟨C, hC⟩` from `main_big hA hP hM hM' hLP hN hAd hX hSo χ`. Use `⟨C, fun h hχ t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩` and prove the remaining obligations.

Take `⟨c₁, h₁⟩` from `exists_coef l (2 ^ (h.nII l ψ + h.nIII l ψ))`. Take `⟨c', hc, hc₁⟩` from `(coefSup l).1 c c₁`. Establish `h₂` using `enough_of_le hc₁ (2 ^ (h.nII l ψ + h.nIII l ψ))`. Set `f : c.O →+* c'.O` to `(Subalgebra.inclusion hc).toRingHom`. Establish `hf : Function.Injective f` using `Subalgebra.inclusion_injective hc`.

Establish `e2 : h.nII l (chHom f ψ) = h.nII l ψ`. Unfold `Host.nII`. Rewrite using `[conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]`. Establish `e3 : h.nIII l (chHom f ψ) = h.nIII l ψ`. Unfold `Host.nIII`.

Rewrite using `[conductor_at_map_injective_coeff f hf]`. Establish `hψ' : chHom f ψ ∈ h.X c' e`. Rewrite `hψ`, the goal using `[h.mem_X]`. Use `⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩` and prove the remaining obligations. Unfold `Host.IsChar`.

Rewrite using `[chHom_ker f hf]`. Conclude with `hψ.1`. Establish `hcase' : h.CaseII l e (chHom f ψ) ∨ h.CaseIII l e (chHom f ψ)`. Break down `hcase with ⟨a, b, d⟩ | ⟨a, b, d, g⟩` into its components or cases. Use `Or.inl ⟨a, ?_, d⟩` and prove the remaining obligations.

Unfold `EV`. Rewrite using `[← chHom_chiP f hf, chHom_ord f hf]`. Conclude with `b`. Conclude with `Or.inr ⟨a, b, (chHom_ord f hf ψ).symm ▸ d, fun h0 => g ((map_eq_one_iff _ (chHom_inj f hf)).1 h0)⟩`. Establish `hV` using `hC h hχ t ht Ω l c' e hl2 he0 het _ hψ' hcase' (e2.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_right _ (h.nIII l ψ)))) (e3.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_left _ (h.nII l ψ))))`.

Take `⟨a, b⟩` from `coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl`. Conclude with `⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩`. Use `⟨fun χ => ?_, fun χ => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `key χ`. Conclude with `⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inl hc)⟩`.

Take `⟨C, hC⟩` from `key χ`. Conclude with `⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inr hc)⟩`.
-/
theorem UpperTheory.V.Th.sp4Main_alt :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense → CohomologyHyp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Af.NumberSp4Alt → _root_.UpperTheory.V.Th.RigiditySymplecticFour → X.CorX → (∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l) → CountII ∧ CountIII := by
  intro hA hP hM hM' hLP hN hAd hX hSo
  have key : CountShape fun h l _ _ e ψ => h.CaseII l e ψ ∨ h.CaseIII l e ψ := by
    intro χ
    obtain ⟨C, hC⟩ := main_big hA hP hM hM' hLP hN hAd hX hSo χ
    refine ⟨C, fun h hχ t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩
    obtain ⟨c₁, h₁⟩ := exists_coef l (2 ^ (h.nII l ψ + h.nIII l ψ))
    obtain ⟨c', hc, hc₁⟩ := (coefSup l).1 c c₁
    have h₂ := enough_of_le hc₁ (2 ^ (h.nII l ψ + h.nIII l ψ))
    let f : c.O →+* c'.O := (Subalgebra.inclusion hc).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hc
    have e2 : h.nII l (chHom f ψ) = h.nII l ψ := by
      unfold Host.nII
      rw [conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]
    have e3 : h.nIII l (chHom f ψ) = h.nIII l ψ := by
      unfold Host.nIII
      rw [conductor_at_map_injective_coeff f hf]
    have hψ' : chHom f ψ ∈ h.X c' e := by
      rw [h.mem_X] at hψ ⊢
      refine ⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩
      unfold Host.IsChar
      rw [chHom_ker f hf]
      exact hψ.1
    have hcase' : h.CaseII l e (chHom f ψ) ∨ h.CaseIII l e (chHom f ψ) := by
      rcases hcase with ⟨a, b, d⟩ | ⟨a, b, d, g⟩
      · refine Or.inl ⟨a, ?_, d⟩
        unfold EV
        rw [← chHom_chiP f hf, chHom_ord f hf]
        exact b
      · exact Or.inr ⟨a, b, (chHom_ord f hf ψ).symm ▸ d, fun h0 => g ((map_eq_one_iff _ (chHom_inj f hf)).1 h0)⟩
    have hV := hC h hχ t ht Ω l c' e hl2 he0 het _ hψ' hcase'
      (e2.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_right _ (h.nIII l ψ))))
      (e3.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_left _ (h.nII l ψ))))
    obtain ⟨a, b⟩ := coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl
    exact ⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩
  refine ⟨fun χ => ?_, fun χ => ?_⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inl hc)⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inr hc)⟩
end

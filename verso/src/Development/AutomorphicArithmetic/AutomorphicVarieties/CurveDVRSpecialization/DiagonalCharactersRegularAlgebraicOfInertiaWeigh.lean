import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩`. Establish `hval : A.valuation (l : Ω) < 1`. Establish `h1` using `(hA (l : 𝓞 F)).2 hl`. Simplify using `using h1`.

Take `⟨u, hu⟩` from `GlobalTheory.CycDec.exists_unit_infinite_order l`. Take `⟨σ, hσI, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval u`. Set `f : ℕ → (F →ₐ[ℚ] Ω)` to `fun k => ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp (IsScalarTower.toAlgHom ℚ F Ω)`. Take `⟨a, b, hab, hfab⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x`.

Introduce `a b hlt he`. Use `⟨b - a, by omega, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x)` using `congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he`. Establish `hb : σ ^ b = σ ^ a * σ ^ (b - a)`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `hx` using `[hb, AlgEquiv.mul_apply]`. Conclude with `((σ ^ a).injective hx).symm`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by`.

Break down `Nat.lt_or_gt_of_ne hab with h | h` into its components or cases. Conclude with `key a b h hfab`. Conclude with `key b a h hfab.symm`. Set `g : G F Ω` to `{ (σ ^ k : Ω ≃ₐ[ℚ] Ω) with commutes' := hk }`. Establish `hgI : g ∈ Ine (F` using `F) A := pow_mem hσI k`.

Use `⟨g, hgI, fun heq => ?_⟩` and prove the remaining obligations. Establish `hr : MulSemiringAction.toRingAut (G F Ω) Ω g = MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ k)` using `RingEquiv.ext fun x => rfl`. Establish `hz : cycZ F Ω l g = u ^ k` using `by show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) = u ^ k`. Rewrite using `[hr, ← hσu, ← map_pow]`. Both sides reduce to the same expression.

Establish `hinj : Function.Injective (Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l))` using `Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)`. Establish `h1 : (u ^ k) ^ n = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zpow, map_one]`. Establish `: cycBar F Ω l g = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (cycZ F Ω l g)` using `rfl`.

Rewrite using `[← hz, ← this]`. Conclude with `heq`. Rewrite `h1` using `[← zpow_natCast, ← zpow_mul]`. Conclude with `hu _ (mul_ne_zero (by exact_mod_cast hk0.ne') hn) h1`.
-/
private theorem cyc_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {v : W.Plc F} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hval : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa using h1
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval u
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k =>
    ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp (IsScalarTower.toAlgHom ℚ F Ω)
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt he
    refine ⟨b - a, by omega, fun x => ?_⟩
    have hx : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, AlgEquiv.mul_apply] at hx
    exact ((σ ^ a).injective hx).symm
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b h hfab
    · exact key b a h hfab.symm
  let g : G F Ω := { (σ ^ k : Ω ≃ₐ[ℚ] Ω) with commutes' := hk }
  have hgI : g ∈ Ine (F := F) A := pow_mem hσI k
  refine ⟨g, hgI, fun heq => ?_⟩
  have hr : MulSemiringAction.toRingAut (G F Ω) Ω g =
      MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ k) := RingEquiv.ext fun x => rfl
  have hz : cycZ F Ω l g = u ^ k := by
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) = u ^ k
    rw [hr, ← hσu, ← map_pow]
    rfl
  have hinj : Function.Injective
      (Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l)) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  have h1 : (u ^ k) ^ n = 1 := by
    apply hinj
    rw [map_zpow, map_one]
    have : cycBar F Ω l g = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (cycZ F Ω l g) := rfl
    rw [← hz, ← this]
    exact heq
  rw [← zpow_natCast, ← zpow_mul] at h1
  exact hu _ (mul_ne_zero (by exact_mod_cast hk0.ne') hn) h1

/- English proof (translation)
Introduce `i j hij`. Establish `: (i : ℕ) < j` using `hij`. Unfold `Fr.w`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem w_anti (n : ℕ) : StrictAnti (Fr.w n) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  unfold Fr.w
  split_ifs <;> omega

/- English proof (translation)
Introduce `hGAR L Ω _ _ _ _ _ l _ ι A w h hl ka hka n m hm κ hκ`. Set `cyc : ↥(Dec (F` to `L) A) →* (Qbar l)ˣ := (cycBar L Ω l).comp (Dec (F := L) A).subtype`. Set `kaD : ↥(Dec (F` to `L) A) →* (Qbar l)ˣ := ka.comp (Dec (F := L) A).subtype`. Take `⟨_, art, χ, a, hart, _, hlad⟩` from `hka`. Set `wk : W.Emb l w → ℤ` to `fun τ => -a ((ι.toRingHom.comp ↑τ).comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)))`.

Establish `hone : IsOpen (((1 : ↥(Ine (F` using `L) A) →* (Qbar l)ˣ).ker : Set ↥(Ine (F := L) A))) := by`. Rewrite using `[MonoidHom.ker_one, Subgroup.coe_top]`. Conclude with `isOpen_univ`. Establish `hkaW : W.IsLocAlg h kaD wk`. Distinguish the cases in `hex : ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a`.

Conclude with `Loc.laHecke h art hart ι χ a ka hlad hex`. Conclude with `⟨1, hone, fun a' ha' => absurd ⟨a', ha'⟩ hex⟩`. Take `⟨phk, hphk⟩` from `hkaW`. Establish `hc` using `Loc.laCyc hGAR h hl`. Take `⟨hmul, hpow, hzero⟩` from `Loc.laMul (l := l) h`.

Establish `hm0 : (0 : ℤ) < m` using `by exact_mod_cast (show 0 < m by omega)`. Establish `hwt : ∀ j, W.IsLocAlg h (κ j * kaD) (fun τ => -((m : ℤ) * Fr.w n j) + wk τ)`. Introduce `j`. Set `x : ℤ` to `(m : ℤ) * Fr.w n j`. Establish `h0 : W.IsWtPart h (κ j * cyc ^ (-x)) 0 1`.

Use `hzero _ _ hone fun σ => ?_` and prove the remaining obligations. Establish `hs` using `hκ j (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)) σ.2`. Rewrite using `[MonoidHom.one_apply, mul_one, MonoidHom.mul_apply, MonoidHom.zpow_apply, hs]`. Use `show cycBar L Ω l σ ^ x * cycBar L Ω l σ ^ (-x) = 1`. Rewrite using `[← zpow_add, add_neg_cancel, zpow_zero]`.

Establish `h1` using `(hmul _ _ _ _ _ _ h0 (hpow _ _ _ x hc)).1`. Establish `h2` using `(hmul _ _ _ _ _ _ h1 hphk).1`. Establish `he : κ j * cyc ^ (-x) * cyc ^ x * kaD = κ j * kaD`. Rewrite using `[mul_assoc (κ j), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]`. Rewrite `h2` using `[he]`.

Use `⟨1 * 1 ^ x * phk, ?_⟩` and prove the remaining obligations. Use `h2 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, x]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨fun j τ => -((m : ℤ) * Fr.w n j) + wk τ, fun τ i j hij => ?_, hwt⟩, ?_⟩` and prove the remaining obligations.

Use `w_anti n hij` as an intermediate fact. Simplify using `only`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i j heq`. Establish `hcomm : κ j * kaD * cyc = κ j * cyc * kaD`.

Rewrite using `[mul_assoc, mul_comm kaD, ← mul_assoc]`. Rewrite `heq` using `[hcomm]`. Establish `heq' : κ i = κ j * cyc` using `mul_right_cancel heq`. Establish `hN : (m : ℤ) * Fr.w n i - (m : ℤ) * Fr.w n j - 1 ≠ 0`. Introduce `h0`.

Establish `h1 : (m : ℤ) * (Fr.w n i - Fr.w n j) = 1` using `by linarith`. Use `Int.eq_one_of_mul_eq_one_right hm0.le h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hne⟩` from `cyc_ine hl h hN`. Apply `hne` to reduce the goal to its premises.

Set `s` to `Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h ⟨g, hg⟩)`. Establish `hi` using `hκ i s hg`. Establish `hj` using `hκ j s hg`. Establish `hs` using `congrArg (fun f => f s) heq'`. Simplify using `only [MonoidHom.mul_apply] at hs`.

Rewrite `hs` using `[hi, hj]`. Establish `hs' : cycBar L Ω l g ^ ((m : ℤ) * Fr.w n i) = cycBar L Ω l g ^ ((m : ℤ) * Fr.w n j) * cycBar L Ω l g` using `hs`. Rewrite using `[zpow_sub, zpow_sub, hs', zpow_one]`. Use `group`.
-/
theorem UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → ∀ (n m : ℕ), 2 ≤ m → ∀ κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ, (∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s = cycBar L Ω l s ^ ((m : ℤ) * Fr.w n i)) → (∃ wt : Fin n → W.Emb l w → ℤ, (∀ τ, StrictMono fun j => wt j τ) ∧ ∀ j, W.IsLocAlg h (κ j * ka.comp (Dec (F := L) A).subtype) (wt j)) ∧ ∀ i j, κ i * ka.comp (Dec (F := L) A).subtype ≠ κ j * ka.comp (Dec (F := L) A).subtype * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  intro hGAR L Ω _ _ _ _ _ l _ ι A w h hl ka hka n m hm κ hκ
  let cyc : ↥(Dec (F := L) A) →* (Qbar l)ˣ := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  let kaD : ↥(Dec (F := L) A) →* (Qbar l)ˣ := ka.comp (Dec (F := L) A).subtype
  obtain ⟨_, art, χ, a, hart, _, hlad⟩ := hka
  let wk : W.Emb l w → ℤ := fun τ =>
    -a ((ι.toRingHom.comp ↑τ).comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)))
  have hone : IsOpen (((1 : ↥(Ine (F := L) A) →* (Qbar l)ˣ).ker : Set ↥(Ine (F := L) A))) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  have hkaW : W.IsLocAlg h kaD wk := by
    by_cases hex : ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a
    · exact Loc.laHecke h art hart ι χ a ka hlad hex
    · exact ⟨1, hone, fun a' ha' => absurd ⟨a', ha'⟩ hex⟩
  obtain ⟨phk, hphk⟩ := hkaW
  have hc := Loc.laCyc hGAR h hl
  obtain ⟨hmul, hpow, hzero⟩ := Loc.laMul (l := l) h
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have hwt : ∀ j, W.IsLocAlg h (κ j * kaD) (fun τ => -((m : ℤ) * Fr.w n j) + wk τ) := by
    intro j
    let x : ℤ := (m : ℤ) * Fr.w n j
    have h0 : W.IsWtPart h (κ j * cyc ^ (-x)) 0 1 := by
      refine hzero _ _ hone fun σ => ?_
      have hs := hκ j (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)) σ.2
      rw [MonoidHom.one_apply, mul_one, MonoidHom.mul_apply, MonoidHom.zpow_apply, hs]
      show cycBar L Ω l σ ^ x * cycBar L Ω l σ ^ (-x) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    have h1 := (hmul _ _ _ _ _ _ h0 (hpow _ _ _ x hc)).1
    have h2 := (hmul _ _ _ _ _ _ h1 hphk).1
    have he : κ j * cyc ^ (-x) * cyc ^ x * kaD = κ j * kaD := by
      rw [mul_assoc (κ j), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [he] at h2
    refine ⟨1 * 1 ^ x * phk, ?_⟩
    convert h2 using 2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, x]
    ring
  refine ⟨⟨fun j τ => -((m : ℤ) * Fr.w n j) + wk τ, fun τ i j hij => ?_, hwt⟩, ?_⟩
  · have := w_anti n hij
    simp only
    nlinarith
  · intro i j heq
    have hcomm : κ j * kaD * cyc = κ j * cyc * kaD := by
      rw [mul_assoc, mul_comm kaD, ← mul_assoc]
    rw [hcomm] at heq
    have heq' : κ i = κ j * cyc := mul_right_cancel heq
    have hN : (m : ℤ) * Fr.w n i - (m : ℤ) * Fr.w n j - 1 ≠ 0 := by
      intro h0
      have h1 : (m : ℤ) * (Fr.w n i - Fr.w n j) = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right hm0.le h1
      omega
    obtain ⟨g, hg, hne⟩ := cyc_ine hl h hN
    apply hne
    let s := Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h ⟨g, hg⟩)
    have hi := hκ i s hg
    have hj := hκ j s hg
    have hs := congrArg (fun f => f s) heq'
    simp only [MonoidHom.mul_apply] at hs
    rw [hi, hj] at hs
    have hs' : cycBar L Ω l g ^ ((m : ℤ) * Fr.w n i) = cycBar L Ω l g ^ ((m : ℤ) * Fr.w n j) * cycBar L Ω l g := hs
    rw [zpow_sub, zpow_sub, hs', zpow_one]
    group

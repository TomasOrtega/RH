import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibreQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

/- English proof (translation)
Use `set q := P.comap (algebraMap S S') with hq`. Establish `hq' : (P.comap φ).comap (algebraMap R R') = q.comap f`. Rewrite using `[hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]`. Establish `hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S')`. Rewrite using `[Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]`.

Set `ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P` to `Localization.localRingHom (P.comap φ) P φ rfl`. Establish `hψ : Function.Surjective ψ`. Introduce `y`. Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl y`. Take `⟨a', rfl⟩` from `hφ a`.

Take `⟨t', ht'⟩` from `hφ (t : S')`. Establish `ht'' : t' ∈ (P.comap φ).primeCompl`. Express the relevant statement in the definitionally equal form `t' ∉ P.comap φ`. Rewrite using `[Ideal.mem_comap, ht']`. Conclude with `t.2`.

Use `⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Localization.localRingHom_mk']`. Use `congr 1`. Conclude with `Subtype.ext ht'`. Set `χ` to `(Ideal.Quotient.mk ((q.map (algebraMap S S')).map (algebraMap S' (Localization.AtPrime P)))).comp ψ`.

Establish `hχ : Function.Surjective χ` using `Ideal.Quotient.mk_surjective.comp hψ`. Establish `hkerχ : ((q.comap f).map (algebraMap R R')).map (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ`. Use extensionality with `x`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (P.comap φ).primeCompl x`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, htr⟩`. Use `⟨φ t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← hmapq]`. Conclude with `Ideal.mem_map_of_mem φ htr`.

Introduce and unpack `⟨t, ht, htr⟩`. Take `⟨t', rfl⟩` from `hφ t`. Use `⟨t', ht, ?_⟩` and prove the remaining obligations. Establish `h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ`. Rewrite using `[hmapq, map_mul]`.

Conclude with `htr`. Rewrite `h1` using `[← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ]`. Establish `key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R')`. Use `le_trans ?_ (le_trans hker (Ideal.map_mono ?_))` and prove the remaining obligations. Introduce `y hy`.

Simplify using `using hy`. Introduce `y hy`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker.mp hy]`. Conclude with `q.zero_mem`. Conclude with `(sup_le le_rfl key) h1`.

Use `⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩` and prove the remaining obligations. Rewrite using `[← hkerχ, hq']`.
-/
theorem primeFibreLocalRing_nonempty_equiv_of_surjective
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by
  set q := P.comap (algebraMap S S') with hq
  have hq' : (P.comap φ).comap (algebraMap R R') = q.comap f := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]
  have hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S') := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  let ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P :=
    Localization.localRingHom (P.comap φ) P φ rfl
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨t', ht'⟩ := hφ (t : S')
    have ht'' : t' ∈ (P.comap φ).primeCompl := by
      change t' ∉ P.comap φ
      rw [Ideal.mem_comap, ht']
      exact t.2
    refine ⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'
  let χ := (Ideal.Quotient.mk ((q.map (algebraMap S S')).map
    (algebraMap S' (Localization.AtPrime P)))).comp ψ
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerχ : ((q.comap f).map (algebraMap R R')).map
      (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ := by
    ext x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap φ).primeCompl x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, htr⟩
      refine ⟨φ t, ht, ?_⟩
      rw [← map_mul, ← hmapq]
      exact Ideal.mem_map_of_mem φ htr
    · rintro ⟨t, ht, htr⟩
      obtain ⟨t', rfl⟩ := hφ t
      refine ⟨t', ht, ?_⟩
      have h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ := by
        rw [hmapq, map_mul]
        exact htr
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ] at h1
      have key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R') := by
        refine le_trans ?_ (le_trans hker (Ideal.map_mono ?_))
        · intro y hy
          simpa using hy
        · intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact q.zero_mem
      exact (sup_le le_rfl key) h1
  refine ⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩
  rw [← hkerχ, hq']

/- English proof (translation)
Use `hB` as an intermediate fact. Establish `: IsNoetherianRing A` using `isNoetherianRing_of_surjective B A f hf`. Use `set M := m.comap f with hM`. Establish `hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n` using `fun n => by`. Rewrite using `[Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]`.

Set `fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n` to `fun n => (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)`. Establish `hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k`. Introduce `k n hle`. Use extensionality with `x`. Proceed by induction on `x using AdicCompletion.induction_on with`.

Consider the case `h b`. Simplify using `only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) = Ideal.Quotient.mk (m ^ k) (f (b k))`. Rewrite using `[Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]`. Establish `hb` using `AdicCompletion.AdicCauchySequence.mk_eq_mk hle b`.

Rewrite `hb` using `[Submodule.Quotient.eq]`. Establish `hb' : b n - b k ∈ M ^ k` using `by simpa using hb`. Rewrite using `[← map_sub]`. Conclude with `Ideal.le_comap_pow f k hb'`. Set `φ : AdicCompletion M B →+* AdicCompletion m A` to `AdicCompletion.liftRingHom m fam hfam`.

Establish `hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f`. Use `RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Simplify using `only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom, RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]`. Both sides reduce to the same expression. Use `⟨φ, ?_, hcomm, ?_⟩` and prove the remaining obligations.

Establish `fgM : M.FG` using `IsNoetherian.noetherian M`. Establish `fgm : m.FG` using `IsNoetherian.noetherian m`. Use `AdicCompletion.isAdicComplete_self M fgM` as an intermediate fact. Establish `hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ = m.map (algebraMap A (AdicCompletion m A))`. Rewrite using `[Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]`.

Establish `: IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A)`. Rewrite using `[hmap]`. Conclude with `(AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff`. Apply `surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ` to reduce the goal to its premises. Introduce `y`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)`. Take `⟨b, rfl⟩` from `hf a`. Use `⟨algebraMap B _ b, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap, ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]`.

Simplify using `[ha, AdicCompletion.algebraMap_apply]`. Introduce `x hx`. Set `_ : Algebra B A` to `f.toAlgebra`. Set `K` to `RingHom.ker f`. Set `g : B →ₗ[B] A` to `Algebra.linearMap B A`.

Establish `hg : Function.Surjective g` using `hf`. Establish `hfg : Function.Exact K.subtype g`. Introduce `y`. Simplify using `[g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]`. Establish `hx' : AdicCompletion.map M g x = 0`.

Proceed by induction on `x using AdicCompletion.induction_on with`. Consider the case `h b => ?_`. Establish `hb` using `RingHom.mem_ker.mp hx`. Use `AdicCompletion.ext fun n => ?_` and prove the remaining obligations. Establish `h1 : f (b n) ∈ m ^ n`.

Use `congrArg (AdicCompletion.evalₐ m n) hb` as an intermediate fact. Rewrite `this` using `[map_zero]`. Simplify using `only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk] at this`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`. Establish `h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A)`.

Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]`. Express the relevant statement in the definitionally equal form `f (b n) ∈ (M ^ n).map f`. Rewrite using `[hpow]`. Conclude with `h1`. Simplify `h2` using `[AdicCompletion.map_mk]`.

Take `⟨z, rfl⟩` from `((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'`. Take `⟨t, rfl⟩` from `AdicCompletion.ofTensorProduct_surjective_of_finite M K z`. Establish `hnat` using `congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply] at hnat`. Rewrite using `[hnat]`.

Use `clear hnat hx hx'`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r k`. Simplify using `only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]`.

Conclude with `Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)`. Consider the case `add t₁ t₂ h₁ h₂`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem h₁ h₂`.
-/
theorem exists_adicCompletion_surjection_of_surjective
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by
  have := hB
  have : IsNoetherianRing A := isNoetherianRing_of_surjective B A f hf
  set M := m.comap f with hM
  have hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n := fun n => by
    rw [Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]
  let fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n := fun n =>
    (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp
      (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)
  have hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k := by
    intro k n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h b =>
      simp only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      change Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) =
        Ideal.Quotient.mk (m ^ k) (f (b k))
      rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have hb := AdicCompletion.AdicCauchySequence.mk_eq_mk hle b
      rw [Submodule.Quotient.eq] at hb
      have hb' : b n - b k ∈ M ^ k := by simpa using hb
      rw [← map_sub]
      exact Ideal.le_comap_pow f k hb'
  let φ : AdicCompletion M B →+* AdicCompletion m A := AdicCompletion.liftRingHom m fam hfam
  have hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f := by
    refine RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom,
      RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  refine ⟨φ, ?_, hcomm, ?_⟩
  · have fgM : M.FG := IsNoetherian.noetherian M
    have fgm : m.FG := IsNoetherian.noetherian m
    have := AdicCompletion.isAdicComplete_self M fgM
    have hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ =
        m.map (algebraMap A (AdicCompletion m A)) := by
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]
    have : IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A) := by
      rw [hmap]
      exact (AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨algebraMap B _ b, ?_⟩
    rw [RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap,
      ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]
    simp [ha, AdicCompletion.algebraMap_apply]
  · intro x hx
    let _ : Algebra B A := f.toAlgebra
    let K := RingHom.ker f
    let g : B →ₗ[B] A := Algebra.linearMap B A
    have hg : Function.Surjective g := hf
    have hfg : Function.Exact K.subtype g := by
      intro y
      simp [g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    have hx' : AdicCompletion.map M g x = 0 := by
      induction x using AdicCompletion.induction_on with
      | h b => ?_
      have hb := RingHom.mem_ker.mp hx
      refine AdicCompletion.ext fun n => ?_
      have h1 : f (b n) ∈ m ^ n := by
        have := congrArg (AdicCompletion.evalₐ m n) hb
        rw [map_zero] at this
        simp only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe,
          AdicCompletion.evalₐ_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        change f (b n) ∈ (M ^ n).map f
        rw [hpow]
        exact h1
      simpa [AdicCompletion.map_mk] using h2
    obtain ⟨z, rfl⟩ := ((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite M K z
    have hnat := congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hnat
    rw [hnat]
    clear hnat hx hx'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
        Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact add_mem h₁ h₂

/- English proof (translation)
Introduce `B A _ _ f hf hB m P _`. Take `⟨φ, hφ, hcomm, hker⟩` from `exists_adicCompletion_surjection_of_surjective f hf hB m`. Use `⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(P.comap φ).comap _ = _`. Rewrite using `[Ideal.comap_comap, hcomm, ← Ideal.comap_comap]`.

Conclude with `primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P`.
-/
theorem FormalFibreQuotient.proof : FormalFibreQuotient.Statement := by
  intro B A _ _ f hf hB m P _
  obtain ⟨φ, hφ, hcomm, hker⟩ := exists_adicCompletion_surjection_of_surjective f hf hB m
  refine ⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩
  · change (P.comap φ).comap _ = _
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  · exact primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

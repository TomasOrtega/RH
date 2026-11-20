import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestWStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

/- English proof (translation)
Establish `: infSpan φ ≤ (infSpan φ).comap (RU E n x)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show RU E n x (RU E n k φ) ∈ infSpan φ`. Rewrite using `[RU_RU]`.

Conclude with `Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩`. Conclude with `this hψ`.
-/
theorem RU_mem_infSpan (φ : UA E n → ℂ) {x : UA E n} (hx : x ∈ infU E n) {ψ : UA E n → ℂ} (hψ : ψ ∈ infSpan φ) :
    RU E n x ψ ∈ infSpan φ := by
  have : infSpan φ ≤ (infSpan φ).comap (RU E n x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show RU E n x (RU E n k φ) ∈ infSpan φ
    rw [RU_RU]
    exact Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩
  exact this hψ

/- English proof (translation)
The claim follows from `(Subgroup.mem_inf.1 hx).1`.
-/
theorem mem_infU_of_mem_embU {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) : x ∈ infU E n :=
  (Subgroup.mem_inf.1 hx).1

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ`. Take `⟨φ, hφU, hφ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot`. Set `j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n` to `(embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom`. Establish `hj : ∀ u, j u ∈ infU E n` using `fun u => mem_infU_of_mem_embU (e.symm u).2`. Set `S` to `infSpan φ`.

Establish `hφS : φ ∈ S`. Establish `: RU E n (1 : infU E n) φ ∈ S` using `Submodule.subset_span ⟨1, rfl⟩`. Simplify using `using this`. Establish `hS : S ≤ U.V` using `Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)`. Use `haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin`.

Use `haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩`. Set `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S` to `sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)`. Establish `hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v` using `fun _ _ => rfl`. Establish `hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v)`. Set `P : Submodule ℂ (Module.Dual ℂ S)` to `{ carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)} add_mem' := fun ha hb v => (ha v).add (hb v) zero_mem' := fun _ => continuous_const smul_mem' := fun c _ ha v => (ha v).const_smul c }`.

Establish `hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P` using `fun g v => by`. Establish `hv : Continuous (v : UA E n → ℂ)` using `(U.isAut.aut _ (hS v.2)).cont`. Establish `: Continuous fun u => (j u : UA E n)` using `continuous_subtype_val.comp e.symm.continuous`. Conclude with `hv.comp ((continuous_const_mul g).comp this)`. Establish `h1 : P.dualCoannihilator = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))`. Establish `hP : P = ⊤`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]`. Introduce `l v`. Establish `: l ∈ P` using `hP ▸ Submodule.mem_top`. Conclude with `this v`. Take `⟨lam, f, hf⟩` from `GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep n S ρ hcont`.

Use `⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_, fun v => hS (f v).2, fun x v => ?_⟩` and prove the remaining obligations. Use `Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)` and prove the remaining obligations. Simplify using `using LinearMap.congr_fun h0 v`. Establish `h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x)` using `(he x).symm`. Rewrite using `[h1]`.

Establish `h2` using `Representation.IntertwiningMap.isIntertwining _ _ f (e x) v`. Express the relevant statement in the definitionally equal form `(f (smallRep (unitaryIncl n) lam (e x) v)).1 = _`. Rewrite using `[h2, hρ]`. Express the relevant statement in the definitionally equal form `RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _`. Rewrite using `[e.symm_apply_apply]`.

Both sides reduce to the same expression.
-/
theorem exists_hasWeightAt (U : AutSub E n) (τ : E →+* ℂ) : ∃ lam, HasWeightAt U.V τ lam := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot
  let j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hj : ∀ u, j u ∈ infU E n := fun u => mem_infU_of_mem_embU (e.symm u).2
  let S := infSpan φ
  have hφS : φ ∈ S := by
    have : RU E n (1 : infU E n) φ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using this
  have hS : S ≤ U.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)
  haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin
  haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S :=
    sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)
  have hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v := fun _ _ => rfl
  have hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v) := by
    let P : Submodule ℂ (Module.Dual ℂ S) :=
      { carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)}
        add_mem' := fun ha hb v => (ha v).add (hb v)
        zero_mem' := fun _ => continuous_const
        smul_mem' := fun c _ ha v => (ha v).const_smul c }
    have hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P := fun g v => by
      have hv : Continuous (v : UA E n → ℂ) := (U.isAut.aut _ (hS v.2)).cont
      have : Continuous fun u => (j u : UA E n) := continuous_subtype_val.comp e.symm.continuous
      exact hv.comp ((continuous_const_mul g).comp this)
    have h1 : P.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))
    have hP : P = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]
    intro l v
    have : l ∈ P := hP ▸ Submodule.mem_top
    exact this v
  obtain ⟨lam, f, hf⟩ := GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep n S ρ hcont
  refine ⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_,
    fun v => hS (f v).2, fun x v => ?_⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)
    simpa using LinearMap.congr_fun h0 v
  · have h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x) := (he x).symm
    rw [h1]
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ f (e x) v
    change (f (smallRep (unitaryIncl n) lam (e x) v)).1 = _
    rw [h2, hρ]
    change RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _
    rw [e.symm_apply_apply]
    rfl

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ`. Take `⟨r, -, hr1, hr⟩` from `GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E n τ`. Set `s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n` to `(embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom`. Establish `mk : ∀ mu, HasWeightAt U.V τ mu → ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0`. Introduce and unpack `mu ⟨-, F, hF0, hFm, hFi⟩`.

Use `⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩` and prove the remaining obligations. Use extensionality with `v : 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)`. Establish `: unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u)`.

Establish `h3` using `he (e.symm u)`. Rewrite `h3` using `[e.apply_symm_apply]`. Conclude with `h3`. Rewrite using `[this, hFi]`. Both sides reduce to the same expression.

Use extensionality with `v : 1`. Conclude with `congrArg Subtype.val (DFunLike.congr_fun h0 v :)`. Take `⟨f, hf⟩` from `mk lam h`. Take `⟨f', hf'⟩` from `mk lam' h'`. Establish `hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)` using `fun g => ⟨e (r g), fun y => by`.

Express the relevant statement in the definitionally equal form `Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)`. Rewrite using `[e.symm_apply_apply]`. Conclude with `hr g _⟩`. Take `⟨ee⟩` from `(GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam) (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'`. Assume the negation of the conclusion as `hne`.

Establish `h0` using `intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap`. Take `⟨v, hv⟩` from `exists_ne (0 : nablaSq ℂ n lam)`. Conclude with `hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))`.
-/
theorem hasWeightAt_unique (U : AutSub E n) (τ : E →+* ℂ) {lam lam' : DomWeight n} (h : HasWeightAt U.V τ lam)
    (h' : HasWeightAt U.V τ lam') : lam = lam' := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E n τ
  let s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ mu, HasWeightAt U.V τ mu →
      ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro mu ⟨-, F, hF0, hFm, hFi⟩
    refine ⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)
      have : unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u) := by
        have h3 := he (e.symm u)
        rw [e.apply_symm_apply] at h3
        exact h3
      rw [this, hFi]
      rfl
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  obtain ⟨f, hf⟩ := mk lam h
  obtain ⟨f', hf'⟩ := mk lam' h'
  have hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨ee⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam)
    (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'
  by_contra hne
  have h0 := intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ n lam)
  exact hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))

/- English proof (translation)
Introduce `E _ _ _ n π τ`. Take `⟨U, rfl⟩` from `AU.mk_surjective π`. Take `⟨lam, h⟩` from `exists_hasWeightAt U τ`. Conclude with `⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩`.
-/
theorem AU.existsUnique_hasWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  intro E _ _ _ n π τ
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨lam, h⟩ := exists_hasWeightAt U τ
  exact ⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩

end GlobalTheory.DefU

end

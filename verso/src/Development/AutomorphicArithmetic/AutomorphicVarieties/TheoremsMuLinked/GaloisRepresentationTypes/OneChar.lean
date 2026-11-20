import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDat
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ULocEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RingEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.VlenLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapReducibleThreeDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

/- English proof (translation)
Introduce `a b h`. Use extensionality with `x`. Apply `hf` to reduce the goal to its premises. Establish `hx` using `congrArg (fun χ : DirichletCharacter O' N => χ (x : ZMod N)) h`. Simplify `hx` using `[chHom, MulChar.ringHomComp_apply]`.
-/
private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) := by
  intro a b h
  ext x
  apply hf
  have hx := congrArg (fun χ : DirichletCharacter O' N => χ (x : ZMod N)) h
  simpa [chHom, MulChar.ringHomComp_apply] using hx

/- English proof (translation)
Use extensionality with `x`. Simplify using `[chHom, HV.comp, MulChar.ringHomComp_apply]`.
-/
private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  ext x
  simp [chHom, HV.comp, MulChar.ringHomComp_apply]

/- English proof (translation)
Establish `ho : orderOf (chHom f χ) = orderOf χ` using `orderOf_injective (chHom f) (chHom_inj f hf) χ`. Establish `hl : chHom f (lPart l χ) = lPart l (chHom f χ)`. Simplify using `only [lPart, map_pow, ho]`. Simplify using `only [chiP, th0, lPrime, map_mul, map_inv, hl, chHom_comp]`.
-/
private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  have ho : orderOf (chHom f χ) = orderOf χ := orderOf_injective (chHom f) (chHom_inj f hf) χ
  have hl : chHom f (lPart l χ) = lPart l (chHom f χ) := by
    simp only [lPart, map_pow, ho]
  simp only [chiP, th0, lPrime, map_mul, map_inv, hl, chHom_comp]

/- English proof (translation)
Establish `hinj` using `chHom_inj (N := N) f hf`. Establish `hord : orderOf (chHom f χ) = orderOf χ` using `orderOf_injective _ hinj χ`. Establish `hine : HV.comp l (chHom f χ) ^ 2 = 1 ↔ HV.comp l χ ^ 2 = 1`. Rewrite using `[← chHom_comp, ← map_pow]`. Conclude with `map_eq_one_iff _ hinj`.

Establish `hpar : PsiEven e (chHom f χ) ↔ PsiEven e χ`. Simplify using `only [PsiEven, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply]`. Rewrite using `[show ((-1 : O') ^ e) = f ((-1) ^ e) by simp, hf.eq_iff]`. Establish `hker : ∀ ψ : DirichletCharacter O N, (Chr.dirG ℚ Ω (chHom f ψ)).ker = (Chr.dirG ℚ Ω ψ).ker`. Introduce `ψ`.

Use extensionality with `σ`. Simplify using `only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply]`. Rewrite using `[Units.ext_iff, Units.ext_iff]`. Simplify using `only [MulChar.coe_toUnitHom, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply, Units.val_one]`. Conclude with `⟨fun h => hf (by rw [h, map_one]), fun h => by rw [h, map_one]⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `heta` using `h.eta`. Rewrite `heta` using `[← chHom_chiP f hf, hker]`. Conclude with `⟨h.l_odd, h.e_pos, h.N_even, by rw [← hord]; exact h.ord, hine.1 h.ine, hpar.1 h.par, h.quad, h.imag, h.l_cop, h.cop, heta, h.gen⟩`.

Introduce `h`. Establish `heta` using `h.eta`. Rewrite `heta` using `[← hker, chHom_chiP f hf]`. Conclude with `⟨h.l_odd, h.e_pos, h.N_even, by rw [hord]; exact h.ord, hine.2 h.ine, hpar.2 h.par, h.quad, h.imag, h.l_cop, h.cop, heta, h.gen⟩`.
-/
private theorem gd_chHom (hf : Function.Injective f) [NeZero N] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {e : ℕ} (χ : DirichletCharacter O N) :
    GD Ω K l e (chHom f χ) ↔ GD Ω K l e χ := by
  have hinj := chHom_inj (N := N) f hf
  have hord : orderOf (chHom f χ) = orderOf χ := orderOf_injective _ hinj χ
  have hine : HV.comp l (chHom f χ) ^ 2 = 1 ↔ HV.comp l χ ^ 2 = 1 := by
    rw [← chHom_comp, ← map_pow]
    exact map_eq_one_iff _ hinj
  have hpar : PsiEven e (chHom f χ) ↔ PsiEven e χ := by
    simp only [PsiEven, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply]
    rw [show ((-1 : O') ^ e) = f ((-1) ^ e) by simp, hf.eq_iff]
  have hker : ∀ ψ : DirichletCharacter O N, (Chr.dirG ℚ Ω (chHom f ψ)).ker = (Chr.dirG ℚ Ω ψ).ker := by
    intro ψ
    ext σ
    simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply]
    rw [Units.ext_iff, Units.ext_iff]
    simp only [MulChar.coe_toUnitHom, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply,
      Units.val_one]
    exact ⟨fun h => hf (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  constructor
  · intro h
    have heta := h.eta
    rw [← chHom_chiP f hf, hker] at heta
    exact ⟨h.l_odd, h.e_pos, h.N_even, by rw [← hord]; exact h.ord, hine.1 h.ine, hpar.1 h.par, h.quad, h.imag,
      h.l_cop, h.cop, heta, h.gen⟩
  · intro h
    have heta := h.eta
    rw [← hker, chHom_chiP f hf] at heta
    exact ⟨h.l_odd, h.e_pos, h.N_even, by rw [hord]; exact h.ord, hine.2 h.ine, hpar.2 h.par, h.quad, h.imag,
      h.l_cop, h.cop, heta, h.gen⟩

end Transfer

/- English proof (translation)
Establish `hn : orderOf ψ ≠ 0`. Introduce `h0`. Conclude with `h (h0 ▸ dvd_zero l)`. Use `haveI : NeZero (orderOf ψ) := ⟨hn⟩`. Establish `hl : ¬ l ∣ orderOf ψ` using `h`.

Take `⟨c', hc'e, hroots⟩` from `(coefSup l).2.1 (orderOf ψ) hl`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (↥c'.O) (orderOf ψ)`. Establish `hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ)` using `hζ.map_of_injective (f := c'.O.val) Subtype.val_injective`. Establish `mem : ∀ u : (ZMod N)ˣ, (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ∈ c'.O`. Introduce `u`.

Establish `h1 : (ψ.toUnitHom u) ^ orderOf ψ = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hn, pow_orderOf_eq_one, MulChar.one_apply (Units.isUnit u), Units.val_one]`. Establish `h2 : (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ^ orderOf ψ = 1`. Establish `h3` using `congrArg (fun y : c.Oˣ => (((y : c.O)) : PadicAlgCl l)) h1`.

Simplify using `using h3`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one h2`. Rewrite using `[← hi]`. Conclude with `pow_mem ζ.2 i`. Set `g : (ZMod N)ˣ →* (↥c'.O)ˣ` to `{ toFun := fun u => ⟨⟨_, mem u⟩, ⟨_, mem u⁻¹⟩, by`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]`. Rewrite using `[← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, OneMemClass.coe_one], by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]`.

Rewrite using `[← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, OneMemClass.coe_one]⟩`. Use the proof step `map_one' := by`. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := by`. Introduce `u v`. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `}`.

Use `⟨c', MulChar.ofUnitHom g, hc'e, fun a => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : IsUnit a`. Take `⟨u, rfl⟩` from `ha`. Rewrite using `[MulChar.ofUnitHom_coe]`. Simplify using `[g, MulChar.coe_toUnitHom]`.

Rewrite using `[MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]`. Simplify using the standard rewrite rules.
-/
private theorem exists_unram {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (h : ¬ l ∣ orderOf ψ) : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
  have hn : orderOf ψ ≠ 0 := by
    intro h0
    exact h (h0 ▸ dvd_zero l)
  haveI : NeZero (orderOf ψ) := ⟨hn⟩
  have hl : ¬ l ∣ orderOf ψ := h
  obtain ⟨c', hc'e, hroots⟩ := (coefSup l).2.1 (orderOf ψ) hl
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (↥c'.O) (orderOf ψ)
  have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
    hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
  have mem : ∀ u : (ZMod N)ˣ, (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ∈ c'.O := by
    intro u
    have h1 : (ψ.toUnitHom u) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hn, pow_orderOf_eq_one,
        MulChar.one_apply (Units.isUnit u), Units.val_one]
    have h2 : (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ^ orderOf ψ = 1 := by
      have h3 := congrArg (fun y : c.Oˣ => (((y : c.O)) : PadicAlgCl l)) h1
      simpa using h3
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h2
    rw [← hi]
    exact pow_mem ζ.2 i
  let g : (ZMod N)ˣ →* (↥c'.O)ˣ :=
    { toFun := fun u => ⟨⟨_, mem u⟩, ⟨_, mem u⁻¹⟩, by
          apply Subtype.ext
          simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
          rw [← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
            OneMemClass.coe_one], by
          apply Subtype.ext
          simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
          rw [← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
            OneMemClass.coe_one]⟩
      map_one' := by
        apply Units.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Units.ext
        apply Subtype.ext
        simp }
  refine ⟨c', MulChar.ofUnitHom g, hc'e, fun a => ?_⟩
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [MulChar.ofUnitHom_coe]
    simp [g, MulChar.coe_toUnitHom]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]
    simp

/- English proof (translation)
Introduce `g` and use `⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩`.
-/
private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ]
    (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

/- English proof (translation)
Simplify using `[GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]`.
-/
private theorem trace_reducible_three_dim {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    (r0 η Ψ g).mat.trace = (Ψ g : R) + 1 + (((Ψ g)⁻¹ : Rˣ) : R) := by
  simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]

/- English proof (translation)
Take `⟨D⟩` from `exists_dat hG`. Take `⟨g₁, hM, hFin, hB, hW⟩` from `hA Ω K l c N e ψ D he ι`. Take `⟨U⟩` from `exists_uLoc hI.toCohInp D`. Take `⟨S⟩` from `exists_ring hI.toCohInp D U g₁ hM`. Take `⟨M⟩` from `exists_model hI.toCohInp hI.lemP D hM S`.

Establish `hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom)` using `fun f g => S.r.hasMult g`. Set `ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l))` to `fun f => D.rhoK (push f S.r.hom) (hmult f)`. Establish `hσ : D.η (galEmb ℚ K Ω σ) = 1`. Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`. Conclude with `galEmb_mem ℚ K Ω σ`.

Establish `htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f = (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t`. Introduce `f`. Rewrite using `[trDiff, trace_reducible_three_dim, ht]`. Use `congr 1`. Conclude with `AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _`.

Establish `hadm : ∀ f, TwoPt D.η S.r.hom f → Af.Adm3 ι e N (ρ f) ∨ Af.Adm2 ι e (N * (discr K).natAbs) (ρ f)`. Introduce `f hf`. Establish `hp` using `isPt_push D hM S f hf.1`. Break down `(twoPt_shape S hG.l_odd hM f hf).1 with h | h` into its components or cases. Conclude with `Or.inl (admissible_rank_three_type_one hI.toCohInp D hM hp ι h (hB U S _ _ _ (isPush_push f _) h))`.

Conclude with `Or.inr (admissible_of_typeII hI.toCohInp D hM hp ι h (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1))`. Take `⟨hlen, T, hT, hTo, hle⟩` from `model_upper S M hG.l_odd hM hI.lemM (hFin U S) (Th.ptHyp_of hI D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))`. Establish `hV` using `vlen_le hI.toCohInp hI.lemM' D hM S M`. Establish `hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f'`. Introduce and unpack `f hf f' hf' ⟨g, hg⟩`.

Take `⟨s, hs⟩` from `(twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by`. Rewrite `hx` using `[D.η_ker, ← range_galEmb]`. Take `⟨y, rfl⟩` from `hx`. Conclude with `(congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩`. Conclude with `hTo f hf f' hf' s hs`.

Use `⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hadm f (hT.1 f hf)`. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨f', hf', rfl⟩` from `Finset.mem_image.1 hx'`.

Rewrite using `[hinj f hf f' hf' h]`. Rewrite using `[Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]`. Simplify using `only [← htr]`. Conclude with `(Chr.nrm_mono l hV hlen).trans hle`.
-/
private theorem oneChar_unram (hI : Th.InpU) (hA : Aut.AutomorphyUnramifiedCoefficients)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (he : eO l c.O = 1) (hG : GD Ω K l e ψ) (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l)
    (ht : t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)))
    (hne : ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), Af.Adm3 ι e N ρ ∨ Af.Adm2 ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) :
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, Af.Adm3 ι e N ρ ∨ Af.Adm2 ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t) := by
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hI.toCohInp D
  obtain ⟨S⟩ := exists_ring hI.toCohInp D U g₁ hM
  obtain ⟨M⟩ := exists_model hI.toCohInp hI.lemP D hM S
  have hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom) := fun f g => S.r.hasMult g
  let ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l)) := fun f => D.rhoK (push f S.r.hom) (hmult f)
  have hσ : D.η (galEmb ℚ K Ω σ) = 1 := by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω σ
  have htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f =
      (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t := by
    intro f
    rw [trDiff, trace_reducible_three_dim, ht]
    congr 1
    exact AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _
  have hadm : ∀ f, TwoPt D.η S.r.hom f → Af.Adm3 ι e N (ρ f) ∨ Af.Adm2 ι e (N * (discr K).natAbs) (ρ f) := by
    intro f hf
    have hp := isPt_push D hM S f hf.1
    rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
    · exact Or.inl (admissible_rank_three_type_one hI.toCohInp D hM hp ι h (hB U S _ _ _ (isPush_push f _) h))
    · exact Or.inr (admissible_of_typeII hI.toCohInp D hM hp ι h
        (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1))
  obtain ⟨hlen, T, hT, hTo, hle⟩ := model_upper S M hG.l_odd hM hI.lemM (hFin U S)
    (Th.ptHyp_of hI D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ
    fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))
  have hV := vlen_le hI.toCohInp hI.lemM' D hM S M
  have hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f' := by
    rintro f hf f' hf' ⟨g, hg⟩
    obtain ⟨s, hs⟩ := (twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by
      rw [D.η_ker, ← range_galEmb] at hx
      obtain ⟨y, rfl⟩ := hx
      exact (congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩
    exact hTo f hf f' hf' s hs
  refine ⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    exact hadm f (hT.1 f hf)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hx'
    rw [hinj f hf f' hf' h]
  · rw [Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]
    simp only [← htr]
    exact (Chr.nrm_mono l hV hlen).trans hle

/- English proof (translation)
Introduce `hI hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne`. Take `⟨c', ψ', he, hψ⟩` from `exists_unram c ψ hG.ord`. Establish `h1 : chHom c.O.val.toRingHom ψ = chHom c'.O.val.toRingHom ψ'` using `MulChar.ext fun a => hψ a`. Establish `hG' : GD Ω K l e ψ'` using `(gd_chHom c'.O.val.toRingHom Subtype.val_injective ψ').1 (h1 ▸ (gd_chHom c.O.val.toRingHom Subtype.val_injective ψ).2 hG)`. Take `⟨h2, h3⟩` from `coefIndep Ω l c c' N e ψ ψ' hψ`.

Establish `h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) = Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g)`. Introduce `g`. Simplify using `only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]`. Use `congr 1`. Conclude with `Units.ext (hψ _)`.

Establish `h5` using `congrArg Units.val (h4 (galEmb ℚ K Ω σ))`. Establish `h6` using `congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))`. Rewrite using `[Ne, h2, h3]`. Use `oneChar_unram hI hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne` and prove the remaining obligations. Rewrite using `[ht, map_add, map_add, map_add, map_add, map_one, map_one]`.

Conclude with `congrArg₂ (· + ·) (congrArg (· + 1) h5) h6`.
-/
theorem UpperTheory.V.Th.oneChar :
    Th.InpU → Aut.AutomorphyUnramifiedCoefficients → OneChar := by
  intro hI hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne
  obtain ⟨c', ψ', he, hψ⟩ := exists_unram c ψ hG.ord
  have h1 : chHom c.O.val.toRingHom ψ = chHom c'.O.val.toRingHom ψ' := MulChar.ext fun a => hψ a
  have hG' : GD Ω K l e ψ' :=
    (gd_chHom c'.O.val.toRingHom Subtype.val_injective ψ').1
      (h1 ▸ (gd_chHom c.O.val.toRingHom Subtype.val_injective ψ).2 hG)
  obtain ⟨h2, h3⟩ := coefIndep Ω l c c' N e ψ ψ' hψ
  have h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) =
      Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g) := by
    intro g
    simp only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]
    congr 1
    exact Units.ext (hψ _)
  have h5 := congrArg Units.val (h4 (galEmb ℚ K Ω σ))
  have h6 := congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))
  rw [Ne, h2, h3]
  refine oneChar_unram hI hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne
  rw [ht, map_add, map_add, map_add, map_add, map_one, map_one]
  exact congrArg₂ (· + ·) (congrArg (· + 1) h5) h6

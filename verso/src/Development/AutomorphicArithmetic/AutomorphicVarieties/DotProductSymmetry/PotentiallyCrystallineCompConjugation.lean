import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
open scoped Pointwise

/- English proof (translation)
Use `haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω`. Establish `h1 : u (algebraMap K Ω x) ∈ (⊥ : IntermediateField K Ω)`. Rewrite using `[← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]`. Introduce `s _`. Take `⟨t, rfl⟩` from `c.surjective s`.

Establish `h2 : (c t) (u (algebraMap K Ω x)) = (u * galEmb ℚ K Ω t * u⁻¹) (u (algebraMap K Ω x))` using `DFunLike.congr_fun (hc t) _`. Establish `h3 : (galEmb ℚ K Ω t) (algebraMap K Ω x) = algebraMap K Ω x` using `t.commutes x`. Rewrite using `[h2]`. Simplify using `[h3]`. Take `⟨y, hy⟩` from `IntermediateField.mem_bot.1 h1`.

Conclude with `⟨y, hy⟩`.
-/
private theorem fixAux {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (u : G ℚ Ω) (c : G K Ω ≃* G K Ω)
    (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹) (x : K) :
    ∃ y : K, algebraMap K Ω y = u (algebraMap K Ω x) := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h1 : u (algebraMap K Ω x) ∈ (⊥ : IntermediateField K Ω) := by
    rw [← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]
    intro s _
    obtain ⟨t, rfl⟩ := c.surjective s
    have h2 : (c t) (u (algebraMap K Ω x)) = (u * galEmb ℚ K Ω t * u⁻¹) (u (algebraMap K Ω x)) :=
      DFunLike.congr_fun (hc t) _
    have h3 : (galEmb ℚ K Ω t) (algebraMap K Ω x) = algebraMap K Ω x := t.commutes x
    rw [h2]
    simp [h3]
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `hgA : u • A' = A`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hu]`. Simplify using `[AlgEquiv.smul_def]`. Rewrite using `[mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]`.
-/
private theorem mem_decomposition_conj_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (u : G ℚ Ω) (A A' : ValuationSubring Ω)
    (hu : ∀ x, x ∈ A' ↔ u x ∈ A) (t : G ℚ Ω) :
    t ∈ Dec (F := ℚ) A' ↔ u * t * u⁻¹ ∈ Dec (F := ℚ) A := by
  have hgA : u • A' = A := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hu]
    simp [AlgEquiv.smul_def]
  rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]

/- English proof (translation)
Take `⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩` from `hA`. Establish `hc' : ∀ s, galEmb ℚ K Ω (c.symm s) = u⁻¹ * galEmb ℚ K Ω s * u` using `fun s => by`. Establish `h` using `hc (c.symm s)`. Rewrite `h` using `[c.apply_symm_apply]`. Rewrite using `[h]`.

Use `group`. Establish `hmem : ∀ s : G K Ω, s ∈ Dec (F` using `K) A' ↔ c s ∈ Dec (F := K) A := fun s => by`. Express the relevant statement in the definitionally equal form `galEmb ℚ K Ω s ∈ Dec (F := ℚ) A' ↔ galEmb ℚ K Ω (c s) ∈ Dec (F := ℚ) A`. Rewrite using `[hc]`. Conclude with `mem_decomposition_conj_iff u A A' hu _`.

Set `φ : ↥(Dec (F` to `K) A') ≃* ↥(Dec (F := K) A) := { toFun := fun s => ⟨c s, (hmem s).1 s.2⟩ invFun := fun t => ⟨c.symm t, (hmem _).2 (by rw [c.apply_symm_apply]; exact t.2)⟩ left_inv := fun s => Subtype.ext (c.symm_apply_apply _) right_inv := fun t => Subtype.ext (c.apply_symm_apply _) map_mul' := …`. Establish `hemb` using `(galEmbTop ℚ K Ω).1`. Establish `hcc : Continuous c` using `hemb.continuous_iff.2 (by`. Establish `e : (galEmb ℚ K Ω) ∘ c = fun s => u * galEmb ℚ K Ω s * u⁻¹` using `funext hc`. Rewrite using `[e]`.

Conclude with `(continuous_const.mul hemb.continuous).mul continuous_const)`. Establish `hcs : Continuous c.symm` using `hemb.continuous_iff.2 (by`. Establish `e : (galEmb ℚ K Ω) ∘ c.symm = fun s => u⁻¹ * galEmb ℚ K Ω s * u` using `funext hc'`. Rewrite using `[e]`. Conclude with `(continuous_const.mul hemb.continuous).mul continuous_const)`.

Establish `hφ : Continuous φ` using `(hcc.comp continuous_subtype_val).subtype_mk _`. Establish `hφs : Continuous φ.symm` using `(hcs.comp continuous_subtype_val).subtype_mk _`. Set `Bw' : LocBridge l K Ω (Dec (F` to `K) A') O := { Kw := Bw.Kw, j := Bw.j.comp (u : Ω →+* Ω) j_E := fun x => by`. Express the relevant statement in the definitionally equal form `Bw.j (u (algebraMap K Ω x)) ∈ _`. Take `⟨y, hy⟩` from `fixAux u c hc x`.

Rewrite using `[← hy]`. Conclude with `Bw.j_E y`. Use `j_dense := Bw.j_dense.trans (closure_mono (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, hy⟩` from `fixAux u⁻¹ c.symm hc' x`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Bw.j (u (algebraMap K Ω y)) = Bw.j (algebraMap K Ω x)`. Rewrite using `[hy]`. Use the proof step `simp))`. Use `e := φ.trans Bw.e`.

Use `e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont`. Use `e_comm := fun s x => by`. Use `(Bw.e_comm (φ s) (u x)).trans ?_` and prove the remaining obligations. Establish `h2 : (c (s : G K Ω)) (u x) = (u * galEmb ℚ K Ω (s : G K Ω) * u⁻¹) (u x)` using `DFunLike.congr_fun (hc s) _`. Express the relevant statement in the definitionally equal form `Bw.j ((c (s : G K Ω)) (u x)) = Bw.j (u ((s : G K Ω) x))`.

Rewrite using `[h2]`. Use `congr 1`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg`.

Use `eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }`. Use `⟨O, i1, i2, i3, Bw', fun x => (hu x).trans (hj (u x)), LL', r'.comp φ.toMonoidHom, ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩` and prove the remaining obligations. Establish `e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r'`. Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Simplify using `[LocBridge.repE, Bw']`.

Rewrite using `[e]`. Conclude with `hcr`.
-/
private theorem partialTrace_valuation_sum {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (u : G ℚ Ω) (c : G K Ω ≃* G K Ω) (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (hu : ∀ x, x ∈ A' ↔ u x ∈ A)
    (hA : PotCrysAt r A) : PotCrysAt (r.comp c.toMonoidHom) A' := by
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hc' : ∀ s, galEmb ℚ K Ω (c.symm s) = u⁻¹ * galEmb ℚ K Ω s * u := fun s => by
    have h := hc (c.symm s)
    rw [c.apply_symm_apply] at h
    rw [h]; group
  have hmem : ∀ s : G K Ω, s ∈ Dec (F := K) A' ↔ c s ∈ Dec (F := K) A := fun s => by
    change galEmb ℚ K Ω s ∈ Dec (F := ℚ) A' ↔ galEmb ℚ K Ω (c s) ∈ Dec (F := ℚ) A
    rw [hc]
    exact mem_decomposition_conj_iff u A A' hu _
  let φ : ↥(Dec (F := K) A') ≃* ↥(Dec (F := K) A) :=
    { toFun := fun s => ⟨c s, (hmem s).1 s.2⟩
      invFun := fun t => ⟨c.symm t, (hmem _).2 (by rw [c.apply_symm_apply]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (c.symm_apply_apply _)
      right_inv := fun t => Subtype.ext (c.apply_symm_apply _)
      map_mul' := fun s t => Subtype.ext (map_mul c _ _) }
  have hemb := (galEmbTop ℚ K Ω).1
  have hcc : Continuous c := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c = fun s => u * galEmb ℚ K Ω s * u⁻¹ := funext hc
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hcs : Continuous c.symm := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c.symm = fun s => u⁻¹ * galEmb ℚ K Ω s * u := funext hc'
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hφ : Continuous φ := (hcc.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := (hcs.comp continuous_subtype_val).subtype_mk _
  let Bw' : LocBridge l K Ω (Dec (F := K) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (u : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (u (algebraMap K Ω x)) ∈ _
        obtain ⟨y, hy⟩ := fixAux u c hc x
        rw [← hy]; exact Bw.j_E y
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := fixAux u⁻¹ c.symm hc' x
        refine ⟨y, ?_⟩
        change Bw.j (u (algebraMap K Ω y)) = Bw.j (algebraMap K Ω x)
        rw [hy]
        simp))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (u x)).trans ?_
        have h2 : (c (s : G K Ω)) (u x) = (u * galEmb ℚ K Ω (s : G K Ω) * u⁻¹) (u x) :=
          DFunLike.congr_fun (hc s) _
        change Bw.j ((c (s : G K Ω)) (u x)) = Bw.j (u ((s : G K Ω) x))
        rw [h2]
        congr 1
        simp
        rfl
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨O, i1, i2, i3, Bw', fun x => (hu x).trans (hj (u x)), LL', r'.comp φ.toMonoidHom,
    ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
  have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
    refine MonoidHom.ext fun t => ?_
    simp [LocBridge.repE, Bw']
  rw [e]
  exact hcr

end

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ _ _ l _ n u c hc r A A' hu hA`. Conclude with `partialTrace_valuation_sum u c hc r A A' hu hA`.
-/
theorem UpperTheory.potentiallyCrystalline_comp_conjugation :
    ∀ {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
        (u : G ℚ Ω) (c : G K Ω ≃* G K Ω), (∀ s, UpperTheory.V.Base.galEmb ℚ K Ω (c s) = u * UpperTheory.V.Base.galEmb ℚ K Ω s * u⁻¹) →
        ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω), (∀ x, x ∈ A' ↔ u x ∈ A) →
          UpperTheory.V.Af.PotCrysAt r A → UpperTheory.V.Af.PotCrysAt (r.comp c.toMonoidHom) A' := by
  intro K Ω _ _ _ _ _ _ _ l _ n u c hc r A A' hu hA
  exact partialTrace_valuation_sum u c hc r A A' hu hA

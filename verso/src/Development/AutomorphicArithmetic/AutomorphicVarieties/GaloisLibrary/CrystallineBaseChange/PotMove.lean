import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ n r A A' g hg hA`. Take `⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩` from `hA`. Establish `hmem : ∀ s : G F Ω, s ∈ Dec (F` using `F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by`. Establish `hgA : g • A' = A`. Use extensionality with `x`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]`. Simplify using `[AlgEquiv.smul_def]`. Rewrite using `[mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]`. Set `φ : ↥(Dec (F` to `F) A') ≃* ↥(Dec (F := F) A) := { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩ invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by`. Establish `e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t` using `by group`.

Rewrite using `[e]`. Conclude with `t.2)⟩`. Use `left_inv := fun s => Subtype.ext (by dsimp only; group)`. Use `right_inv := fun t => Subtype.ext (by dsimp only; group)`. Use the proof step `map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }`.

Establish `hφ : Continuous φ` using `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _`. Establish `hφs : Continuous φ.symm` using `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _`. Establish `hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x)` using `fun x => by`. Rewrite using `[AlgEquiv.commutes]`. Set `Bw' : LocBridge l F Ω (Dec (F` to `F) A') O := { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω) j_E := fun x => by`.

Express the relevant statement in the definitionally equal form `Bw.j (g (algebraMap F Ω x)) ∈ _`. Rewrite using `[hjE]`. Conclude with `Bw.j_E x`. Use `j_dense := Bw.j_dense.trans (closure_mono (by`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `⟨x, hjE x⟩))`. Use `e := φ.trans Bw.e`. Use `e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont`. Use `e_comm := fun s x => by`. Use `(Bw.e_comm (φ s) (g x)).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))`. Simplify using the standard rewrite rules. Use `LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg`. Use `eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }`. Establish `h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A'`.

Use `⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom, ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩` and prove the remaining obligations. Establish `e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r'`. Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Simplify using `[LocBridge.repE, Bw']`. Rewrite using `[e]`.

Conclude with `hcr`. Use `h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
theorem UpperTheory.V.Br.potMove :
    UpperTheory.V.Br.PotMove := by
  intro F Ω _ _ _ _ _ l _ n r A A' g hg hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hmem : ∀ s : G F Ω, s ∈ Dec (F := F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by
    have hgA : g • A' = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]
      simp [AlgEquiv.smul_def]
    rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]
  let φ : ↥(Dec (F := F) A') ≃* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩
      invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by
        have e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t := by group
        rw [e]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group)
      map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x) := fun x => by
    rw [AlgEquiv.commutes]
  let Bw' : LocBridge l F Ω (Dec (F := F) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (g (algebraMap F Ω x)) ∈ _
        rw [hjE]; exact Bw.j_E x
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, hjE x⟩))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (g x)).trans ?_
        change Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))
        simp
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A' := by
    refine ⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom,
      ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
    have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
      refine MonoidHom.ext fun t => ?_
      simp [LocBridge.repE, Bw']
    rw [e]
    exact hcr
  refine h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩
  simp [mul_assoc]

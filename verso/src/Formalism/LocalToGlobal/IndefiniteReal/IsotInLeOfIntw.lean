import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Indep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

/- English proof (translation)
Establish `h1` using `hp.herm (y + z) x`. Establish `h2` using `hp.herm y x`. Establish `h3` using `hp.herm z x`. Establish `h4` using `hp.add y z x`. Simplify using `only [Submodule.coe_add] at h1 h4`.

Rewrite using `[← h1, ← h2, ← h3, h4, map_add]`.
-/
theorem hp_add_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y z : C) :
    ip x ((y : A) + z) = ip x y + ip x z := by
  have h1 := hp.herm (y + z) x
  have h2 := hp.herm y x
  have h3 := hp.herm z x
  have h4 := hp.add y z x
  simp only [Submodule.coe_add] at h1 h4
  rw [← h1, ← h2, ← h3, h4, map_add]

/- English proof (translation)
Establish `h` using `hp_add_right hp x 0 0`. Simplify using `only [ZeroMemClass.coe_zero, add_zero] at h`. Take the linear combination `-h`.
-/
theorem hp_zero_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) : ip x (0 : A) = 0 := by
  have h := hp_add_right hp x 0 0
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  linear_combination -h

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty]`. Conclude with `hp_zero_right hp x`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`.

Establish `h` using `hp_add_right hp x (w a) (∑ i ∈ s, w i)`. Rewrite `h` using `[Submodule.coe_sum]`. Conclude with `h`.
-/
theorem hp_sum_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) {ι : Type}
    (s : Finset ι) (w : ι → C) : ip x (∑ i ∈ s, (w i : A)) = ∑ i ∈ s, ip x (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hp_zero_right hp x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := hp_add_right hp x (w a) (∑ i ∈ s, w i)
    rw [Submodule.coe_sum] at h
    exact h

/- English proof (translation)
Rewrite using `[iSupIndep_def]`. Introduce `i`. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hxS`. Establish `hs : ∀ (s : ℂ) (y : C), ip (x : A) ((s • y : C) : A) = s * ip (x : A) (y : A)`.

Introduce `s y`. Rewrite using `[← hp.herm (s • y) x, Submodule.coe_smul, hp.smul s y x, map_mul, Complex.conj_conj, hp.herm y x]`. Set `ℓ : C →ₗ[ℂ] ℂ` to `{ toFun := fun y => ip (x : A) (y : A) map_add' := fun y z => by`. Simplify using `only [Submodule.coe_add]`. Conclude with `hp_add_right hp x y z`.

Use the proof step `map_smul' := fun s y => by`. Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Conclude with `hs s y }`. Establish `hle : (⨆ (j : ι) (_ : j ≠ i), W j) ≤ LinearMap.ker ℓ`. Use `iSup₂_le fun j hj y hy => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker]`. Conclude with `horth i j (Ne.symm hj) x hx y hy`. Establish `h0 : ip (x : A) (x : A) = 0` using `hle hxS`. Assume the negation of the conclusion as `hne`. Use `hp.pos x hne` as an intermediate fact.

Rewrite `this` using `[h0, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem iSupIndep_of_orth {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) {ι : Type}
    (W : ι → Submodule ℂ C) (horth : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, ip x y = 0) : iSupIndep W := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hxS
  have hs : ∀ (s : ℂ) (y : C), ip (x : A) ((s • y : C) : A) = s * ip (x : A) (y : A) := by
    intro s y
    rw [← hp.herm (s • y) x, Submodule.coe_smul, hp.smul s y x, map_mul, Complex.conj_conj, hp.herm y x]
  let ℓ : C →ₗ[ℂ] ℂ :=
    { toFun := fun y => ip (x : A) (y : A)
      map_add' := fun y z => by
        simp only [Submodule.coe_add]
        exact hp_add_right hp x y z
      map_smul' := fun s y => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact hs s y }
  have hle : (⨆ (j : ι) (_ : j ≠ i), W j) ≤ LinearMap.ker ℓ := by
    refine iSup₂_le fun j hj y hy => ?_
    rw [LinearMap.mem_ker]
    exact horth i j (Ne.symm hj) x hx y hy
  have h0 : ip (x : A) (x : A) = 0 := hle hxS
  by_contra hne
  have := hp.pos x hne
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

end Indep

section F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostF (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {n : ℕ}

/- English proof (translation)
Unfold `isotIn`. Use `iSup₂_le fun Φ hΦ => ?_` and prove the remaining obligations. Establish `hr : LinearMap.range (Φ.comp T) = LinearMap.range Φ`. Rewrite using `[LinearMap.range_comp, hsurj, Submodule.map_top]`. Rewrite using `[← hr]`.

Use `le_iSup₂ (f := fun (Ψ : π'.S →ₗ[ℂ] A) (_ : IsEqvA ρ π' Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ) (Φ.comp T) ⟨?_, hr ▸ hΦ.2⟩` and prove the remaining obligations. Introduce `h f`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hT h f]`. Conclude with `hΦ.1 h (T f)`.
-/
theorem isotIn_le_of_intw {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (T : π'.S →ₗ[ℂ] π.S) (hT : Intw π' π T)
    (hsurj : LinearMap.range T = ⊤) : isotIn ρ C π ≤ isotIn ρ C π' := by
  unfold isotIn
  refine iSup₂_le fun Φ hΦ => ?_
  have hr : LinearMap.range (Φ.comp T) = LinearMap.range Φ := by
    rw [LinearMap.range_comp, hsurj, Submodule.map_top]
  rw [← hr]
  refine le_iSup₂ (f := fun (Ψ : π'.S →ₗ[ℂ] A) (_ : IsEqvA ρ π' Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ)
    (Φ.comp T) ⟨?_, hr ▸ hΦ.2⟩
  intro h f
  simp only [LinearMap.comp_apply]
  rw [hT h f]
  exact hΦ.1 h (T f)

/- English proof (translation)
Unfold `Formalism.L2.NG.FinTyp.Iso Formalism.L2.NG.IsoRep at h`. Take `⟨T, hT⟩` from `h`. Apply `le_antisymm` to reduce the goal to its premises. Use `isotIn_le_of_intw ρ C (T.symm : π'.S →ₗ[ℂ] π.S) ?_ (LinearMap.range_eq_top.2 T.symm.surjective)` and prove the remaining obligations. Introduce `h f`.

Establish `key : T ⟨_, π.stable h _ (T.symm f).2⟩ = ⟨_, π'.stable h _ f.2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT h (T.symm f) ⟨_, π.stable h _ (T.symm f).2⟩ rfl, LinearEquiv.apply_symm_apply]`. Conclude with `T.symm_apply_eq.2 key.symm`. Use `isotIn_le_of_intw ρ C (T : π.S →ₗ[ℂ] π'.S) ?_ (LinearMap.range_eq_top.2 T.surjective)` and prove the remaining obligations.

Introduce `h f`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hT h f ⟨_, π.stable h _ f.2⟩ rfl`.
-/
theorem isotIn_iso {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') : isotIn ρ C π = isotIn ρ C π' := by
  unfold Formalism.L2.NG.FinTyp.Iso Formalism.L2.NG.IsoRep at h
  obtain ⟨T, hT⟩ := h
  apply le_antisymm
  · refine isotIn_le_of_intw ρ C (T.symm : π'.S →ₗ[ℂ] π.S) ?_ (LinearMap.range_eq_top.2 T.symm.surjective)
    intro h f
    have key : T ⟨_, π.stable h _ (T.symm f).2⟩ = ⟨_, π'.stable h _ f.2⟩ := by
      apply Subtype.ext
      rw [hT h (T.symm f) ⟨_, π.stable h _ (T.symm f).2⟩ rfl, LinearEquiv.apply_symm_apply]
    exact T.symm_apply_eq.2 key.symm
  · refine isotIn_le_of_intw ρ C (T : π.S →ₗ[ℂ] π'.S) ?_ (LinearMap.range_eq_top.2 T.surjective)
    intro h f
    apply Subtype.ext
    exact hT h f ⟨_, π.stable h _ f.2⟩ rfl

variable {Y W : Formalism.BasicNotions.TH.HSp D} {SpY SpW : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

/- English proof (translation)
Unfold `isotL`. Rewrite using `[isotIn_iso (actM P M) (Minf θ P M) h]`.
-/
theorem isotL_iso (P : RowPsi W n) (M : Mult.DSModel W SpW) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (e : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') :
    isotL θ P M J χ e π = isotL θ P M J χ e π' := by
  unfold isotL
  rw [isotIn_iso (actM P M) (Minf θ P M) h]

open Classical in

def IsotF (PY : RowPsi Y n) (MY : Mult.DSModel Y SpY) (JY : Bool → Set (GA D Y)) (χY : Bool → GA D Y → ℂ)
    (eY : Bool → (GA D Y → ℂ) →ₗ[ℂ] (GA D Y → ℂ)) (PW : RowPsi W n) (MW : Mult.DSModel W SpW) (JW : Set (GA D W))
    (χW : GA D W → ℂ) (eW : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) : Prop :=
  DirectSum.IsInternal (fun σ : FTR θ PY MY JY χY eY =>
    (isotL θ PW MW JW χW eW (rowRepR θ σ)).comap (Mult.goodPart θ MW JW χW eW).subtype)

open Classical in

/- English proof (translation)
Unfold `IsotF`. Rewrite using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Establish `hle : ∀ π, isotL θ PW MW JW χW eW π ≤ Mult.goodPart θ MW JW χW eW` using `fun π => by`. Unfold `isotL`. Conclude with `inf_le_left`.

Prove the components needed by the constructor for the conclusion. Use `iSupIndep_of_orth hp _ ?_` and prove the remaining obligations. Introduce `σ σ' hne x hx y hy`. Use `hD.2 (rowRepR θ σ) (rowRepR θ σ') ?_ x hx y hy` and prove the remaining obligations. Introduce `hiso`.

Apply `hne` to reduce the goal to its premises. Conclude with `Quotient.out_equiv_out.1 hiso`. Establish `hmap : ∀ σ : FTR θ PY MY JY χY eY, ((isotL θ PW MW JW χW eW (rowRepR θ σ)).comap (Mult.goodPart θ MW JW χW eW).subtype).map (Mult.goodPart θ MW JW χW eW).subtype = isotL θ PW MW JW χW eW (rowRepR θ σ)` using `fun σ => by`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 (hle _)`.

Establish `hGle : Mult.goodPart θ MW JW χW eW ≤ (⨆ σ : FTR θ PY MY JY χY eY, (isotL θ PW MW JW χW eW (rowRepR θ σ)).comap (Mult.goodPart θ MW JW χW eW).subtype).map (Mult.goodPart θ MW JW χW eW).subtype`. Rewrite using `[Submodule.map_iSup]`. Simplify using `only [hmap]`. Rewrite using `[hD.1]`. Use `iSup_le fun π => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : isotL θ PW MW JW χW eW π = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`. Take `⟨σ, hσ⟩` from `hocc π h0`. Rewrite using `[← isotL_iso θ PW MW JW χW eW hσ]`.

Conclude with `le_iSup (fun σ => isotL θ PW MW JW χW eW (rowRepR θ σ)) σ`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨y, hy, hxy⟩` from `hGle x.2`. Establish `h2 : (y : Mult.MMap MW) = x` using `hxy`.

Establish `h3 : y = x` using `Subtype.ext h2`. Rewrite using `[← h3]`. Conclude with `hy`.
-/
theorem isotF_of (PY : RowPsi Y n) (MY : Mult.DSModel Y SpY) (JY : Bool → Set (GA D Y)) (χY : Bool → GA D Y → ℂ)
    (eY : Bool → (GA D Y → ℂ) →ₗ[ℂ] (GA D Y → ℂ)) (PW : RowPsi W n) (MW : Mult.DSModel W SpW) (JW : Set (GA D W))
    (χW : GA D W → ℂ) (eW : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) {μ : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hD : IsotDecomp θ PW MW JW χW eW μ 𝓕)
    (hp : PeterssonHilbertSpace.IsHermPos (Mult.goodPart θ MW JW χW eW) (Mult.ipM MW μ 𝓕))
    (hocc : ∀ π, isotL θ PW MW JW χW eW π ≠ ⊥ → ∃ σ : FTR θ PY MY JY χY eY, (rowRepR θ σ).Iso π) :
    IsotF θ PY MY JY χY eY PW MW JW χW eW := by
  unfold IsotF
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hle : ∀ π, isotL θ PW MW JW χW eW π ≤ Mult.goodPart θ MW JW χW eW := fun π => by
    unfold isotL
    exact inf_le_left
  constructor
  · refine iSupIndep_of_orth hp _ ?_
    intro σ σ' hne x hx y hy
    refine hD.2 (rowRepR θ σ) (rowRepR θ σ') ?_ x hx y hy
    intro hiso
    apply hne
    exact Quotient.out_equiv_out.1 hiso
  · have hmap : ∀ σ : FTR θ PY MY JY χY eY,
        ((isotL θ PW MW JW χW eW (rowRepR θ σ)).comap (Mult.goodPart θ MW JW χW eW).subtype).map
          (Mult.goodPart θ MW JW χW eW).subtype = isotL θ PW MW JW χW eW (rowRepR θ σ) := fun σ => by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hle _)
    have hGle : Mult.goodPart θ MW JW χW eW ≤
        (⨆ σ : FTR θ PY MY JY χY eY,
          (isotL θ PW MW JW χW eW (rowRepR θ σ)).comap (Mult.goodPart θ MW JW χW eW).subtype).map
          (Mult.goodPart θ MW JW χW eW).subtype := by
      rw [Submodule.map_iSup]
      simp only [hmap]
      rw [hD.1]
      refine iSup_le fun π => ?_
      by_cases h0 : isotL θ PW MW JW χW eW π = ⊥
      · rw [h0]
        exact bot_le
      · obtain ⟨σ, hσ⟩ := hocc π h0
        rw [← isotL_iso θ PW MW JW χW eW hσ]
        exact le_iSup (fun σ => isotL θ PW MW JW χW eW (rowRepR θ σ)) σ
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hxy⟩ := hGle x.2
    have h2 : (y : Mult.MMap MW) = x := hxy
    have h3 : y = x := Subtype.ext h2
    rw [← h3]
    exact hy

end F

end Formalism.IndefR.principalLevelFrame

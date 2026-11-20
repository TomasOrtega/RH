import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car}

/- English proof (translation)
Simplify using `[SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]`.
-/
theorem mem_smulLat {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (x : Fin n → D.host.E) : x ∈ SDLat.smulLat γ L ↔ ∃ w ∈ L, γ *ᵥ w = x := by
  simp [SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA'`. Apply `Submodule.subset_span` to reduce the goal to its premises. Introduce `x hx`. Take `⟨w, hw, rfl⟩` from `(mem_smulLat γ L x).1 hx`.

Use `(mem_smulLat γ' L' _).2 ⟨A *ᵥ w, hA' w hw, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]`. Consider the case `zero => simp`. Consider the case `add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb`. Consider the case `smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha`.
-/
theorem homL_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.homL D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  induction hA using Submodule.span_induction with
  | mem A hA' =>
    apply Submodule.subset_span
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (mem_smulLat γ L x).1 hx
    refine (mem_smulLat γ' L' _).2 ⟨A *ᵥ w, hA' w hw, ?_⟩
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]
  | zero => simp
  | add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb
  | smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨a, ha, A, hA, rfl⟩` from `hB`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨a, ha, _, homL_conj γ γ' h1 hA, by simp [Matrix.mul_smul, Matrix.smul_mul]⟩`.

Consider the case `zero => simp`. Consider the case `add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb`. Consider the case `smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha`.
-/
theorem yy_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.YYl D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨a, ha, _, homL_conj γ γ' h1 hA, by simp [Matrix.mul_smul, Matrix.smul_mul]⟩
  | zero => simp
  | add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb
  | smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Establish `hm : (γ' * A * star γ).map (TaylorLogMetric.embT D τ) = gM γ' τ * of (fun i j => TaylorLogMetric.embT D τ (A i j)) * (gM γ τ)ᴴ`. Rewrite using `[gM_conjTranspose]`. Simplify using `only [gM, Matrix.map_mul]`. Both sides reduce to the same expression.

Conclude with `congrFun (congrFun hm i) j`.
-/
theorem embV_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (A : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (letI := D.host.cmStar; γ' * A * star γ) =
      phiL γ γ' h1 h2 h1' h2' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) := by
  funext τ i j
  have hm : (γ' * A * star γ).map (TaylorLogMetric.embT D τ) =
      gM γ' τ * of (fun i j => TaylorLogMetric.embT D τ (A i j)) * (gM γ τ)ᴴ := by
    rw [gM_conjTranspose]
    simp only [gM, Matrix.map_mul]
    rfl
  exact congrFun (congrFun hm i) j

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_smulLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨v, hv, rfl⟩, rfl⟩`. Rewrite using `[Matrix.mulVec_mulVec, h, Matrix.one_mulVec]` and apply the resulting hypothesis.

Introduce `hx`. Conclude with `⟨γ *ᵥ x, ⟨x, hx, rfl⟩, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩`.
-/
private theorem smulLat_star_smulLat_of_unitary {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : star γ * γ = 1)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : SDLat.smulLat (star γ) (SDLat.smulLat γ L) = L := by
  ext x
  simp only [mem_smulLat]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  · intro hx
    exact ⟨γ *ᵥ x, ⟨x, hx, rfl⟩, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[imgLat, AddSubgroup.map_le_iff_le_comap]`. Apply `(AddSubgroup.closure_le _).2` to reduce the goal to its premises. Introduce and unpack `z ⟨w, hw, A, hA, rfl⟩`. Express the relevant statement in the definitionally equal form `phiL γ γ' h1 h2 h1' h2' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L')`.

Rewrite using `[map_smul, ← embV_conj γ γ' h1 h2 h1' h2']`. Conclude with `AddSubgroup.subset_closure ⟨w, hw, _, yy_conj γ γ' h1 hA, rfl⟩`. Apply `(AddSubgroup.closure_le _).2` to reduce the goal to its premises. Introduce and unpack `z ⟨w, hw, B, hB, rfl⟩`. Establish `hB'` using `yy_conj (star γ) (star γ') (by rw [star_star]; exact h2) hB`.

Rewrite `hB'` using `[smulLat_star_smulLat_of_unitary γ h1, smulLat_star_smulLat_of_unitary γ' h1']`. Use `⟨w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (star γ' * B * star (star γ)), AddSubgroup.subset_closure ⟨w, hw, _, hB', rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `phiL γ γ' h1 h2 h1' h2' _ = _`. Rewrite using `[map_smul, ← embV_conj γ γ' h1 h2 h1' h2']`. Use `congr 2`.

Simplify using `only [star_star, ← Matrix.mul_assoc, h2', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem la_img {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    imgLat ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  apply le_antisymm
  · rw [imgLat, AddSubgroup.map_le_iff_le_comap]
    apply (AddSubgroup.closure_le _).2
    rintro z ⟨w, hw, A, hA, rfl⟩
    change phiL γ γ' h1 h2 h1' h2' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) ∈
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L')
    rw [map_smul, ← embV_conj γ γ' h1 h2 h1' h2']
    exact AddSubgroup.subset_closure ⟨w, hw, _, yy_conj γ γ' h1 hA, rfl⟩
  · apply (AddSubgroup.closure_le _).2
    rintro z ⟨w, hw, B, hB, rfl⟩
    have hB' := yy_conj (star γ) (star γ') (by rw [star_star]; exact h2) hB
    rw [smulLat_star_smulLat_of_unitary γ h1, smulLat_star_smulLat_of_unitary γ' h1'] at hB'
    refine ⟨w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (star γ' * B * star (star γ)),
      AddSubgroup.subset_closure ⟨w, hw, _, hB', rfl⟩, ?_⟩
    change phiL γ γ' h1 h2 h1' h2' _ = _
    rw [map_smul, ← embV_conj γ γ' h1 h2 h1' h2']
    congr 2
    simp only [star_star, ← Matrix.mul_assoc, h2', Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Hf_eq' (T : TaylorLogMetric.Tor D) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Hf D T z w = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pull_eq {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (F : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' F = pullInv (phiL γ γ' h1 h2 h1' h2') F := rfl

/- English proof (translation)
Establish `h` using `phiL_isom γ γ' h1 h2 h1' h2' (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) x x`. Simplify using `only [LinearEquiv.coe_coe] at h`. Simplify using `only [TaylorLogMetric.al, Hf_eq']`. Rewrite using `[h]`.
-/
theorem al_phi {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (x : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (phiL γ γ' h1 h2 h1' h2' x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x := by
  have h := phiL_isom γ γ' h1 h2 h1' h2' (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) x x
  simp only [LinearEquiv.coe_coe] at h
  simp only [TaylorLogMetric.al, Hf_eq']
  rw [h]

/- English proof (translation)
Establish `hmem : ∀ (Λ : AddSubgroup V) (a : V), φ a ∈ imgLat (φ : V →ₗ[ℂ] V) Λ ↔ a ∈ Λ` using `fun Λ a => AddSubgroup.mem_map_iff_mem (f := (φ : V →ₗ[ℂ] V).toAddMonoidHom) φ.injective`. Set `e0 : Λ₂ ≃ imgLat (φ : V →ₗ[ℂ] V) Λ₂` to `Equiv.subtypeEquiv φ.toEquiv (fun a => (hmem Λ₂ a).symm)`. Establish `hrelq : ∀ a b : Λ₂, (-a + b ∈ Λ₁.addSubgroupOf Λ₂ ↔ -(e0 a) + e0 b ∈ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂))`. Introduce `a b`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]`.

Establish `h5 : ((-(e0 a) + e0 b : imgLat (φ : V →ₗ[ℂ] V) Λ₂) : V) = φ ((-a + b : Λ₂) : V)`. Simplify using `[e0]`. Rewrite using `[h5, hmem]`. Set `e : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃ (imgLat (φ : V →ₗ[ℂ] V) Λ₂ ⧸ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂))` to `Quotient.congr e0 (fun a b => by`. Rewrite using `[QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]`.

Conclude with `hrelq a b)`. Establish `hidx : (Λ₁.addSubgroupOf Λ₂).index = ((imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)).index` using `Nat.card_congr e`. Rewrite using `[hidx]`. Use `congr 1`. Rewrite using `[← finsum_comp_equiv e]`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `q`. Establish `hq : e q = QuotientAddGroup.mk (e0 (Quotient.out q))` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `hrel` using `QuotientAddGroup.eq.mp ((QuotientAddGroup.out_eq' (e q)).trans hq)`.

Rewrite `hrel` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨x, hφx⟩ : ∃ x, φ x = ↑(Quotient.out (e q))` from `⟨_, φ.apply_symm_apply _⟩`. Establish `hxΛ : x ∈ Λ₂`. Rewrite using `[← hmem, hφx]`. Conclude with `(Quotient.out (e q)).2`.

Establish `hy : x - ↑(Quotient.out q) ∈ Λ₁`. Establish `h3 : φ (-(x - ↑(Quotient.out q))) ∈ imgLat (φ : V →ₗ[ℂ] V) Λ₁`. Use `hrel using 1` and compare the differences between its conclusion and the goal. Simplify using `[e0, hφx]`. Normalize the expressions using the abelian group laws.

Rewrite `h3` using `[hmem, neg_mem_iff]`. Then use the resulting hypothesis. Rewrite using `[← hφx, hα, ← pullOpU V H φ hI x G z]`. Simplify using `only [pullInv]`. Establish `h4` using `hcl (↑(Quotient.out q)) (Quotient.out q).2 (x - ↑(Quotient.out q)) (sub_mem hxΛ (Quotient.out q).2) hy (φ.symm z)`. Establish `h6 : (↑(Quotient.out q) : V) + (x - ↑(Quotient.out q)) = x` using `by abel`.

Rewrite `h4` using `[h6]`. Conclude with `h4.symm`.
-/
private theorem pull_core_lemma {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ)
    (φ : V ≃ₗ[ℂ] V) (hI : IsIsom H H (φ : V →ₗ[ℂ] V)) (hα : ∀ x, α (φ x) = α x)
    (Λ₁ Λ₂ : AddSubgroup V) (G : V → ℂ)
    (hcl : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, y ∈ Λ₁ → ∀ z, α (x + y) * opU H (x + y) G z = α x * opU H x G z) (z : V) :
    (((Real.sqrt ((Λ₁.addSubgroupOf Λ₂).index : ℝ)) : ℂ))⁻¹ *
        ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, α ↑(Quotient.out q) * opU H ↑(Quotient.out q) G (φ.symm z) =
      (((Real.sqrt (((imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)).index : ℝ)) : ℂ))⁻¹ *
        ∑ᶠ q : imgLat (φ : V →ₗ[ℂ] V) Λ₂ ⧸ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂),
          α ↑(Quotient.out q) * opU H ↑(Quotient.out q) (pullInv φ G) z := by
  have hmem : ∀ (Λ : AddSubgroup V) (a : V), φ a ∈ imgLat (φ : V →ₗ[ℂ] V) Λ ↔ a ∈ Λ := fun Λ a =>
    AddSubgroup.mem_map_iff_mem (f := (φ : V →ₗ[ℂ] V).toAddMonoidHom) φ.injective
  let e0 : Λ₂ ≃ imgLat (φ : V →ₗ[ℂ] V) Λ₂ := Equiv.subtypeEquiv φ.toEquiv (fun a => (hmem Λ₂ a).symm)
  have hrelq : ∀ a b : Λ₂, (-a + b ∈ Λ₁.addSubgroupOf Λ₂ ↔
      -(e0 a) + e0 b ∈ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)) := by
    intro a b
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]
    have h5 : ((-(e0 a) + e0 b : imgLat (φ : V →ₗ[ℂ] V) Λ₂) : V) = φ ((-a + b : Λ₂) : V) := by
      simp [e0]
    rw [h5, hmem]
  let e : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃ (imgLat (φ : V →ₗ[ℂ] V) Λ₂ ⧸
      (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)) :=
    Quotient.congr e0 (fun a b => by
      rw [QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
      exact hrelq a b)
  have hidx : (Λ₁.addSubgroupOf Λ₂).index =
      ((imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)).index := Nat.card_congr e
  rw [hidx]
  congr 1
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro q
  have hq : e q = QuotientAddGroup.mk (e0 (Quotient.out q)) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  have hrel := QuotientAddGroup.eq.mp ((QuotientAddGroup.out_eq' (e q)).trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hrel
  obtain ⟨x, hφx⟩ : ∃ x, φ x = ↑(Quotient.out (e q)) := ⟨_, φ.apply_symm_apply _⟩
  have hxΛ : x ∈ Λ₂ := by
    rw [← hmem, hφx]
    exact (Quotient.out (e q)).2
  have hy : x - ↑(Quotient.out q) ∈ Λ₁ := by
    have h3 : φ (-(x - ↑(Quotient.out q))) ∈ imgLat (φ : V →ₗ[ℂ] V) Λ₁ := by
      convert hrel using 1
      simp [e0, hφx]
      abel
    rwa [hmem, neg_mem_iff] at h3
  rw [← hφx, hα, ← pullOpU V H φ hI x G z]
  simp only [pullInv]
  have h4 := hcl (↑(Quotient.out q)) (Quotient.out q).2 (x - ↑(Quotient.out q))
    (sub_mem hxΛ (Quotient.out q).2) hy (φ.symm z)
  have h6 : (↑(Quotient.out q) : V) + (x - ↑(Quotient.out q)) = x := by abel
  rw [h6] at h4
  exact h4.symm

/- English proof (translation)
Establish `hUo : ∀ (x : TaylorLogMetric.VC D N N') (F : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N'), TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x F z = opU (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') x F z`. Introduce `x F z`. Simplify using `only [TaylorLogMetric.U, opU, Hf_eq']`. Establish `hG1 : Differentiable ℂ G` using `hG.1`. Establish `hG2 : ∀ x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L', ∀ z, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x G z = G z` using `hG.2`.

Simplify using `only [TaylorLogMetric.Th]`. Rewrite using `[← i1, ← i2]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `hG1.comp (LinearMap.toContinuousLinearMap (φ.symm : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')).differentiable`. Introduce and unpack `_ ⟨y, hy, rfl⟩ z`.

Express the relevant statement in the definitionally equal form `TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ y) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (φ y) (pullInv φ G) z = pullInv φ G z`. Rewrite using `[hα, hUo, ← pullOpU _ _ φ hI y G z]`. Simplify using `only [pullInv]`. Rewrite using `[← hUo]`. Conclude with `hG2 y hy _`.

Use function extensionality and compare the values at `z`. Establish `hsemi` using `(hL.1 N N' L₁ L₁' a2).2`. Establish `hfix : G ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L')`. Introduce `x hx z`. Rewrite using `[← hUo]`.

Conclude with `hG2 x hx z`. Establish `hcl` using `interClass (TaylorLogMetric.VC D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (formV_herm _ _ _ _) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') (TaylorLogM …`. Simplify using `only [TaylorLogMetric.Iop, hUo]`. Conclude with `pull_core_lemma _ _ φ hI hα _ _ G hcl z`.
-/
theorem pull_core {B : Cd.Base D cc δ} (hL : B.LatAll) {N N' : ℕ} (φ : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N')
    (hI : IsIsom (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N'))
    (hα : ∀ x, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x)
    {L L₁ M M₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' M' M₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L L') (a2 : TaylorLogMetric.admitted D N N' L₁ L₁')
    (i1 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M')
    (i2 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁')
    (G : TaylorLogMetric.VC D N N' → ℂ) (hG : G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L') :
    pullInv φ G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) M M' ∧
      pullInv φ (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') G) =
        TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁') (pullInv φ G) := by
  have hUo : ∀ (x : TaylorLogMetric.VC D N N') (F : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N'),
      TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x F z =
        opU (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') x F z := by
    intro x F z
    simp only [TaylorLogMetric.U, opU, Hf_eq']
  have hG1 : Differentiable ℂ G := hG.1
  have hG2 : ∀ x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L', ∀ z,
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x G z = G z := hG.2
  simp only [TaylorLogMetric.Th]
  rw [← i1, ← i2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hG1.comp (LinearMap.toContinuousLinearMap (φ.symm : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')).differentiable
  · rintro _ ⟨y, hy, rfl⟩ z
    change TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ y) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (φ y) (pullInv φ G) z = pullInv φ G z
    rw [hα, hUo, ← pullOpU _ _ φ hI y G z]
    simp only [pullInv]
    rw [← hUo]
    exact hG2 y hy _
  · funext z
    have hsemi := (hL.1 N N' L₁ L₁' a2).2
    have hfix : G ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
        (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') := by
      intro x hx z
      rw [← hUo]
      exact hG2 x hx z
    have hcl := interClass (TaylorLogMetric.VC D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (formV_herm _ _ _ _) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁')
      (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) hsemi G hfix
    simp only [TaylorLogMetric.Iop, hUo]
    exact pull_core_lemma _ _ φ hI hα _ _ G hcl z

/- English proof (translation)
Introduce `N N' L L₁ L' L₁' γ γ' hN hN' hSL hSL₁ hSL' hSL₁' G hG`. Establish `h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1` using `Unitary.star_mul_self_of_mem γ.2`. Establish `h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1` using `Unitary.mul_star_self_of_mem γ.2`. Establish `h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1` using `Unitary.star_mul_self_of_mem γ'.2`. Establish `h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1` using `Unitary.mul_star_self_of_mem γ'.2`.

Simplify using `only [Cd.Base.tor, pull_eq (cc := cc) (δ := δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) h1 h2 h1' h2']`. Conclude with `pull_core hL (phiL _ _ h1 h2 h1' h2') (phiL_isom _ _ h1 h2 h1' h2' _) (al_phi _ _ h1 h2 h1' h2') ⟨hN, hN', hSL, hSL'⟩ ⟨hN, hN', hSL₁, hSL₁'⟩ (la_img _ _ h1 h2 h1' h2' L L') (la_img _ _ h1 h2 h1' h2' L₁ L₁') G hG`.
-/
theorem pullIop_of {B : Cd.Base D cc δ} (hL : B.LatAll) : PullIop D B.tor := by
  intro N N' L L₁ L' L₁' γ γ' hN hN' hSL hSL₁ hSL' hSL₁' G hG
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Unitary.star_mul_self_of_mem γ.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Unitary.mul_star_self_of_mem γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Unitary.star_mul_self_of_mem γ'.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Unitary.mul_star_self_of_mem γ'.2
  simp only [Cd.Base.tor, pull_eq (cc := cc) (δ := δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) h1 h2 h1' h2']
  exact pull_core hL (phiL _ _ h1 h2 h1' h2') (phiL_isom _ _ h1 h2 h1' h2' _) (al_phi _ _ h1 h2 h1' h2')
    ⟨hN, hN', hSL, hSL'⟩ ⟨hN, hN', hSL₁, hSL₁'⟩ (la_img _ _ h1 h2 h1' h2' L L') (la_img _ _ h1 h2 h1' h2' L₁ L₁') G hG

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

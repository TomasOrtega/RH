import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Use `latIn_isLattice C v O hv Ω _ _ (hX.fg.map _) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← LatBasic.eigProj_of_mem hx]`. Establish `h : x ∈ Submodule.span C (X : Set Ω)` using `by rw [hX.span_eq_top]; trivial`. Establish `h2` using `Submodule.mem_map_of_mem (f := eigProj ρ σ) h`. Rewrite `h2` using `[Submodule.map_span]`.

Conclude with `h2`.
-/
theorem eigQuot_lattice {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (ρ : 𝓞 E →+* Module.End C Ω) (σ : E →+* C) (X : Submodule O Ω) (hX : X.IsLattice C) :
    (latIn (eigQuot ρ σ X) (eigSp ρ σ)).IsLattice C := by
  refine latIn_isLattice C v O hv Ω _ _ (hX.fg.map _) fun x hx => ?_
  rw [← LatBasic.eigProj_of_mem hx]
  have h : x ∈ Submodule.span C (X : Set Ω) := by rw [hX.span_eq_top]; trivial
  have h2 := Submodule.mem_map_of_mem (f := eigProj ρ σ) h
  rw [Submodule.map_span] at h2
  exact h2

/- English proof (translation)
Introduce `C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ`. Use `⟨Submodule.map_mono ?_, ?_, eigQuot_lattice hv _ _ _ (PtBasic.om'_lattice P), eigQuot_lattice hv _ _ _ P.om_lat⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `P.ht_mem x hx`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Take `⟨x, hx, e⟩` from `P.κ_mem y hy`. Conclude with `⟨κ • y, ⟨x, hx, e⟩, map_smul _ _ _⟩`.
-/
theorem pt_om_block : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C), P.omHT σ ≤ P.omRec σ ∧ (∀ x ∈ P.omRec σ, κ • x ∈ P.omHT σ) ∧ (latIn (P.omHT σ) (P.Ωsp σ)).IsLattice C ∧ (latIn (P.omRec σ) (P.Ωsp σ)).IsLattice C := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ
  refine ⟨Submodule.map_mono ?_, ?_, eigQuot_lattice hv _ _ _ (PtBasic.om'_lattice P),
    eigQuot_lattice hv _ _ _ P.om_lat⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, e⟩ := P.κ_mem y hy
    exact ⟨κ • y, ⟨x, hx, e⟩, map_smul _ _ _⟩

section

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

/- English proof (translation)
Establish `h : ∀ a : 𝓞 E, P.e x (P.ρ a y) = σ (c (a : E)) * P.e x y`. Introduce `a`. Establish `h1` using `P.adj (RingOfIntegers.mapRingEquiv c a) x y`. Establish `h2 : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a` using `by ext; exact hc _`. Rewrite `h1` using `[h2, LatBasic.mem_eigSp.1 hx, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `h1.symm`. Simplify using `only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul, ← mul_assoc]`. Rewrite using `[← Finset.sum_mul]`. Establish `: ∑ k, (σ.comp c.toRingHom) (dualInt E k) * σ (c ((RingOfIntegers.basis E k : 𝓞 E) : E)) = 1`. Rewrite using `[← map_one (σ.comp c.toRingHom), ← LatBasic.sum_dualInt_mul, map_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[this, one_mul]`.
-/
theorem e_eigProj (hc : ∀ x, c (c x) = x) (σ : E →+* C) {x : V} (hx : x ∈ eigSp P.ρ σ) (y : V) :
    P.e x (eigProj P.ρ (σ.comp c.toRingHom) y) = P.e x y := by
  have h : ∀ a : 𝓞 E, P.e x (P.ρ a y) = σ (c (a : E)) * P.e x y := by
    intro a
    have h1 := P.adj (RingOfIntegers.mapRingEquiv c a) x y
    have h2 : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      ext; exact hc _
    rw [h2, LatBasic.mem_eigSp.1 hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact h1.symm
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
    ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, (σ.comp c.toRingHom) (dualInt E k) * σ (c ((RingOfIntegers.basis E k : 𝓞 E) : E)) = 1 := by
    rw [← map_one (σ.comp c.toRingHom), ← LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

/- English proof (translation)
Take `⟨h1, d, -, -, h2⟩` from `exists_diff_generator C v O hv E σ`. Take `⟨-, -, h3, h4⟩` from `SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d hv.hom_inj h1 h2 P.free`. Rewrite using `[← h4, finrank_span_eq_card h3, Fintype.card_fin]`.
-/
theorem finrank_eigSp [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (eigSp P.ρ σ) = N := by
  obtain ⟨h1, d, -, -, h2⟩ := exists_diff_generator C v O hv E σ
  obtain ⟨-, -, h3, h4⟩ := SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d
    hv.hom_inj h1 h2 P.free
  rw [← h4, finrank_span_eq_card h3, Fintype.card_fin]

/- English proof (translation)
Use `haveI := PtBasic.finite_V P`. Set `f` to `P.ht ∘ₗ (eigSp P.ρ σ).subtype`. Establish `h` using `f.finrank_range_add_finrank_ker`. Establish `hr : LinearMap.range f = P.Ωsp σ`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩`. Express the relevant statement in the definitionally equal form `P.ht x ∈ eigSp _ _`. Rewrite using `[← LatBasic.eigProj_of_mem x.2, PtBasic.ht_eigProj]`. Conclude with `LatBasic.eigProj_mem _ _ _`. Introduce `y hy`.

Take `⟨x, rfl⟩` from `PtBasic.ht_surjective P y`. Use `⟨⟨_, LatBasic.eigProj_mem P.ρ σ x⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.ht (eigProj P.ρ σ x) = _`. Rewrite using `[PtBasic.ht_eigProj, LatBasic.eigProj_of_mem hy]`. Establish `hk : finrank C (LinearMap.ker f) = finrank C (P.Wsp σ)`.

Rewrite using `[← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype, inf_comm]`. Both sides reduce to the same expression. Rewrite `h` using `[hr, hk, finrank_eigSp P hv]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_W_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Ωsp σ) = N := by
  haveI := PtBasic.finite_V P
  let f := P.ht ∘ₗ (eigSp P.ρ σ).subtype
  have h := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = P.Ωsp σ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change P.ht x ∈ eigSp _ _
      rw [← LatBasic.eigProj_of_mem x.2, PtBasic.ht_eigProj]
      exact LatBasic.eigProj_mem _ _ _
    · intro y hy
      obtain ⟨x, rfl⟩ := PtBasic.ht_surjective P y
      refine ⟨⟨_, LatBasic.eigProj_mem P.ρ σ x⟩, ?_⟩
      change P.ht (eigProj P.ρ σ x) = _
      rw [PtBasic.ht_eigProj, LatBasic.eigProj_of_mem hy]
  have hk : finrank C (LinearMap.ker f) = finrank C (P.Wsp σ) := by
    rw [← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype,
      inf_comm]
    rfl
  rw [hr, hk, finrank_eigSp P hv] at h
  omega

/- English proof (translation)
Use `haveI := PtBasic.finite_V P`. Use `set τ := σ.comp c.toRingHom`. Set `B : eigSp P.ρ σ →ₗ[C] Module.Dual C (eigSp P.ρ τ)` to `(P.e.domRestrict₁₂ (eigSp P.ρ σ) (eigSp P.ρ τ))`. Establish `hinj : Function.Injective B`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `x hx`. Establish `: (x : V) = 0` using `P.nondeg _ fun y => by`. Rewrite using `[PtBasic.e_skew, ← e_eigProj P hc σ x.2, neg_eq_zero]`. Conclude with `congrArg (fun φ => φ ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩) (LinearMap.mem_ker.1 hx)`. Conclude with `Subtype.ext this`.

Establish `hsurj : Function.Surjective B` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by`. Rewrite using `[Subspace.dual_finrank_eq, finrank_eigSp P hv, finrank_eigSp P hv])).1 hinj`. Set `W₁ : Submodule C (eigSp P.ρ σ)` to `P.W.comap (eigSp P.ρ σ).subtype`. Set `W₂ : Submodule C (eigSp P.ρ τ)` to `P.W.comap (eigSp P.ρ τ).subtype`. Establish `hW : W₁ = W₂.dualAnnihilator.comap B`.

Use extensionality with `x`. Rewrite using `[Submodule.mem_comap (f := B), Submodule.mem_dualAnnihilator]`. Express the relevant statement in the definitionally equal form `P.ht x = 0 ↔ _`. Rewrite using `[P.lagr]`. Use `⟨fun h w hw => h w hw, fun h y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[← e_eigProj P hc σ x.2]`. Use `h ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.ht (eigProj P.ρ τ y) = 0`. Rewrite using `[PtBasic.ht_eigProj, hy, map_zero]`. Establish `e1 : finrank C W₁ = finrank C W₂.dualAnnihilator`.

Rewrite using `[← (LinearEquiv.ofBijective B ⟨hinj, hsurj⟩).finrank_map_eq W₁, hW]`. Conclude with `congrArg (fun U : Submodule C (Module.Dual C (eigSp P.ρ τ)) => finrank C U) (Submodule.map_comap_eq_of_surjective hsurj _)`. Establish `e2` using `Subspace.finrank_add_finrank_dualAnnihilator_eq W₂`. Establish `e3 : ∀ s : E →+* C, finrank C (P.W.comap (eigSp P.ρ s).subtype) = finrank C (P.Wsp s)`. Introduce `s`.

Rewrite using `[← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]`. Both sides reduce to the same expression. Rewrite `e2` using `[← e1, finrank_eigSp P hv, e3, e3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_W_add_conj [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Wsp (σ.comp c.toRingHom)) = N := by
  haveI := PtBasic.finite_V P
  set τ := σ.comp c.toRingHom
  let B : eigSp P.ρ σ →ₗ[C] Module.Dual C (eigSp P.ρ τ) :=
    (P.e.domRestrict₁₂ (eigSp P.ρ σ) (eigSp P.ρ τ))
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have : (x : V) = 0 := P.nondeg _ fun y => by
      rw [PtBasic.e_skew, ← e_eigProj P hc σ x.2, neg_eq_zero]
      exact congrArg (fun φ => φ ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩) (LinearMap.mem_ker.1 hx)
    exact Subtype.ext this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, finrank_eigSp P hv, finrank_eigSp P hv])).1 hinj
  let W₁ : Submodule C (eigSp P.ρ σ) := P.W.comap (eigSp P.ρ σ).subtype
  let W₂ : Submodule C (eigSp P.ρ τ) := P.W.comap (eigSp P.ρ τ).subtype
  have hW : W₁ = W₂.dualAnnihilator.comap B := by
    ext x
    rw [Submodule.mem_comap (f := B), Submodule.mem_dualAnnihilator]
    change P.ht x = 0 ↔ _
    rw [P.lagr]
    refine ⟨fun h w hw => h w hw, fun h y hy => ?_⟩
    rw [← e_eigProj P hc σ x.2]
    refine h ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩ ?_
    change P.ht (eigProj P.ρ τ y) = 0
    rw [PtBasic.ht_eigProj, hy, map_zero]
  have e1 : finrank C W₁ = finrank C W₂.dualAnnihilator := by
    rw [← (LinearEquiv.ofBijective B ⟨hinj, hsurj⟩).finrank_map_eq W₁, hW]
    exact congrArg (fun U : Submodule C (Module.Dual C (eigSp P.ρ τ)) => finrank C U)
      (Submodule.map_comap_eq_of_surjective hsurj _)
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W₂
  have e3 : ∀ s : E →+* C, finrank C (P.W.comap (eigSp P.ρ s).subtype) = finrank C (P.Wsp s) := by
    intro s
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
    rfl
  rw [← e1, finrank_eigSp P hv, e3, e3] at e2
  omega

/- English proof (translation)
Establish `h1` using `finrank_W_add_Ω P hv σ`. Establish `h2` using `finrank_W_add_Ω P hv (σ.comp c.toRingHom)`. Establish `h3` using `finrank_W_add_conj P hv hc σ`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_Ω_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Ωsp σ) + finrank C (P.Ωsp (σ.comp c.toRingHom)) = N := by
  have h1 := finrank_W_add_Ω P hv σ
  have h2 := finrank_W_add_Ω P hv (σ.comp c.toRingHom)
  have h3 := finrank_W_add_conj P hv hc σ
  omega

end

end PositivityTheory.HtPt.Gb

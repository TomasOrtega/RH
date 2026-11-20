import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValGlue

open GlobalTheory.RealMult.RuleDescend (detCorr_comp isPullBy_comp)

/- English proof (translation)
Establish `hf' : Set.range f ⊆ Set.range hW.fromSpec` using `by rwa [hW.range_fromSpec]`. Use `⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')).hom, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')) ≫ _ = _`. Rewrite using `[Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem exists_spMap_fromSpec {M : Scheme.{0}} {W : M.Opens} (hW : IsAffineOpen W) {T : Type} [CommRing T]
    (f : Sp T ⟶ M) (hf : Set.range f ⊆ (W : Set M)) : ∃ ψ : Γ(M, W) →+* T, spMap ψ ≫ hW.fromSpec = f := by
  have hf' : Set.range f ⊆ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')).hom, ?_⟩
  change Spec.map (Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')) ≫ _ = _
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Use `⟨{g | ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M)}, ?_, fun g hg ↦ hg⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `p : PrimeSpectrum R` to `⟨m, hm.isPrime⟩`. Take `⟨W, hW, hx⟩` from `hP (b p)`.

Set `O : Set (PrimeSpectrum R)` to `(b ⁻¹ᵁ W).carrier`. Establish `ho : IsOpen O` using `(b ⁻¹ᵁ W).isOpen`. Take `⟨_, ⟨g, rfl⟩, hpg, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ O from hx) ho`. Use `hpg (hle (Ideal.subset_span ⟨W, hW, ?_⟩))` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Establish `hq : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R))`. Rewrite using `[← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`. Conclude with `⟨q, rfl⟩`. Conclude with `hsub hq`.
-/
theorem exists_span_eq_top {R : Type} [CommRing R] {M : Scheme.{0}} (b : Sp R ⟶ M) (P : M.Opens → Prop)
    (hP : ∀ x : M, ∃ W, P W ∧ x ∈ W) : ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M) := by
  refine ⟨{g | ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M)}, ?_,
    fun g hg ↦ hg⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  obtain ⟨W, hW, hx⟩ := hP (b p)
  let O : Set (PrimeSpectrum R) := (b ⁻¹ᵁ W).carrier
  have ho : IsOpen O := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ O from hx) ho
  refine hpg (hle (Ideal.subset_span ⟨W, hW, ?_⟩))
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact ⟨q, rfl⟩
  exact hsub hq

/- English proof (translation)
Use `Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs v fun g h ↦ ?_` and prove the remaining obligations. Use `hv g h (Localization.Away (g.1 * h.1)) (IsLocalization.Away.awayToAwayRight g.1 h.1) (IsLocalization.Away.awayToAwayLeft h.1 g.1) (RingHom.ext fun r ↦ ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]`.
-/
theorem existsUnique_glue {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤)
    (v : ∀ g : s, Localization.Away (g : R))
    (hv : ∀ (g h : s) (T : Type) [CommRing T] (f₁ : Localization.Away (g : R) →+* T)
      (f₂ : Localization.Away (h : R) →+* T), f₁.comp (algebraMap R _) = f₂.comp (algebraMap R _) →
      f₁ (v g) = f₂ (v h)) :
    ∃! x : R, ∀ g : s, algebraMap R (Localization.Away (g : R)) x = v g := by
  refine Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs v fun g h ↦ ?_
  refine hv g h (Localization.Away (g.1 * h.1)) (IsLocalization.Away.awayToAwayRight g.1 h.1)
    (IsLocalization.Away.awayToAwayLeft h.1 g.1) (RingHom.ext fun r ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq]

/- English proof (translation)
The claim follows from `(existsUnique_glue hs (fun _ ↦ algebraMap R _ y) fun _ _ _ _ _ _ e ↦ RingHom.congr_fun e y).unique h fun _ ↦ rfl`.
-/
theorem eq_of_loc {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤) {x y : R}
    (h : ∀ g : s, algebraMap R (Localization.Away (g : R)) x = algebraMap R _ y) : x = y :=
  (existsUnique_glue hs (fun _ ↦ algebraMap R _ y) fun _ _ _ _ _ _ e ↦ RingHom.congr_fun e y).unique h fun _ ↦ rfl

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `zero => simp`. Consider the case `tmul r a => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`.
-/
theorem tensorEval_comp {R₀ A R R' : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] [CommRing R']
    [Algebra R₀ R'] (ψ : A →+* R) (τ : R →ₐ[R₀] R') (h : R₀ ⊗[ℤ] A) :
    tensorEval ((τ : R →+* R').comp ψ) h = τ (tensorEval ψ h) := by
  induction h with
  | zero => simp
  | tmul r a => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

/- English proof (translation)
Use `haveI := X.invertible_detOmega`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : δ'.1 ∈ Submodule.span R {δ.1})`. Use `⟨a, ha.symm, fun c hc ↦ eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})`. Rewrite using `[smul_comm, ← hc, smul_comm a, ha]`.
-/
theorem existsUnique_smul {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) :
    ∃! u : R, δ'.1 = u • δ.1 := by
  haveI := X.invertible_detOmega
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : δ'.1 ∈ Submodule.span R {δ.1})
  refine ⟨a, ha.symm, fun c hc ↦ eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm, ← hc, smul_comm a, ha]

/- English proof (translation)
Take `⟨δ'', -, hu''⟩` from `hX.existsUnique_detGen ψ δY`. Take `⟨u, -, hu'⟩` from `existsUnique_smul δ δ''`. Use `⟨u ^ k * tensorEval ψ h, fun δ₃ u₃ h₃ e₃ ↦ ?_⟩` and prove the remaining obligations. Take `rfl` from `hu'' δ₃ h₃`. Take `rfl` from `hu' u₃ e₃`.

Both sides reduce to the same expression.
-/
theorem presVal_exists {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) :
    ∃ v, IsPresVal k δY h δ ψ χ v := by
  obtain ⟨δ'', -, hu''⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, -, hu'⟩ := existsUnique_smul δ δ''
  refine ⟨u ^ k * tensorEval ψ h, fun δ₃ u₃ h₃ e₃ ↦ ?_⟩
  obtain rfl := hu'' δ₃ h₃
  obtain rfl := hu' u₃ e₃
  rfl

/- English proof (translation)
Take `⟨δ'', h'', -⟩` from `hX.existsUnique_detGen ψ δY`. Take `⟨u, hu, -⟩` from `existsUnique_smul δ δ''`. Rewrite using `[h₁ δ'' u h'' hu, h₂ δ'' u h'' hu]`.
-/
theorem presVal_unique {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) {v₁ v₂ : R}
    (h₁ : IsPresVal k δY h δ ψ χ v₁) (h₂ : IsPresVal k δY h δ ψ χ v₂) : v₁ = v₂ := by
  obtain ⟨δ'', h'', -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ δ''
  rw [h₁ δ'' u h'' hu, h₂ δ'' u h'' hu]

/- English proof (translation)
Introduce `ε' u' hε' hu'`. Take `⟨ε, hε, -⟩` from `hX.existsUnique_detGen ψ δY`. Take `⟨u, hu, -⟩` from `existsUnique_smul δ ε`. Establish `hun : IsUnit (τ u)` using `(RuleDescend.isUnit_of_eq_smul δ ε u hu).map τ`. Set `ε'' : X'.DetGen` to `⟨τ u • δ'.1, (Submodule.span_singleton_smul_eq hun _).trans δ'.2⟩`.

Establish `d : Obj.DetCorr (τ : R →+* R') θ ε.1 ε''.1` using `fun w w' hw ↦ by`. Express the relevant statement in the definitionally equal form `τ u • δ'.1 w' = _`. Rewrite using `[hδ' w w' hw, hu]`. Simplify using the standard rewrite rules. Take `rfl : ε' = ε''` from `((isPullBy_comp hX hX').existsUnique_detGen _ δY).unique hε' (detCorr_comp hX hX' hε d)`.

Take `rfl : u' = τ u` from `(existsUnique_smul δ' ε'').unique hu' rfl`. Rewrite using `[hv ε u hε hu, map_mul, map_pow, tensorEval_comp]`.
-/
theorem presVal_pull {R₀ : Type} [CommRing R₀] {k : ℕ} {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    {δY : Y.DetGen} {h : R₀ ⊗[ℤ] A} {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    {δ : X.DetGen} {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} {v : R} (hX : X.IsPullBy Y (spMap ψ) χ)
    (hv : IsPresVal k δY h δ ψ χ v) {R' : Type} [CommRing R'] [Algebra R₀ R'] (τ : R →ₐ[R₀] R')
    {X' : Obj F 𝔠 (Sp R')} {θ : X'.A.left ⟶ X.A.left} {δ' : X'.DetGen}
    (hX' : X'.IsPullBy X (spMap (τ : R →+* R')) θ) (hδ' : Obj.DetCorr (τ : R →+* R') θ δ.1 δ'.1) :
    IsPresVal k δY h δ' ((τ : R →+* R').comp ψ) (θ ≫ χ) (τ v) := by
  intro ε' u' hε' hu'
  obtain ⟨ε, hε, -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ ε
  have hun : IsUnit (τ u) := (RuleDescend.isUnit_of_eq_smul δ ε u hu).map τ
  let ε'' : X'.DetGen := ⟨τ u • δ'.1, (Submodule.span_singleton_smul_eq hun _).trans δ'.2⟩
  have d : Obj.DetCorr (τ : R →+* R') θ ε.1 ε''.1 := fun w w' hw ↦ by
    change τ u • δ'.1 w' = _
    rw [hδ' w w' hw, hu]
    simp
  obtain rfl : ε' = ε'' :=
    ((isPullBy_comp hX hX').existsUnique_detGen _ δY).unique hε' (detCorr_comp hX hX' hε d)
  obtain rfl : u' = τ u := (existsUnique_smul δ' ε'').unique hu' rfl
  rw [hv ε u hε hu, map_mul, map_pow, tensorEval_comp]

/- English proof (translation)
Take `⟨δ₃, h₃, -⟩` from `hψ.existsUnique_detGen τ δ'`. Take `rfl : δ'' = δ₃` from `((isPullBy_comp hφ hψ).existsUnique_detGen _ δ).unique h'' (detCorr_comp hφ hψ h' h₃)`. Conclude with `h₃`.
-/
theorem detCorr_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
    {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')}
    {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (hφ : X'.IsPullBy X (spMap σ) φ) (hψ : X''.IsPullBy X' (spMap τ) ψ)
    {δ : X.DetGen} {δ' : X'.DetGen} {δ'' : X''.DetGen} (h' : Obj.DetCorr σ φ δ.1 δ'.1)
    (h'' : Obj.DetCorr (τ.comp σ) (ψ ≫ φ) δ.1 δ''.1) : Obj.DetCorr τ ψ δ'.1 δ''.1 := by
  obtain ⟨δ₃, h₃, -⟩ := hψ.existsUnique_detGen τ δ'
  obtain rfl : δ'' = δ₃ :=
    ((isPullBy_comp hφ hψ).existsUnique_detGen _ δ).unique h'' (detCorr_comp hφ hψ h' h₃)
  exact h₃

/- English proof (translation)
Introduce `F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ H1 H2 R _ _ X hlev δ`. Establish `hN : IsUnit (N : R)` using `hlev.1`. Take `⟨β⟩` from `hlev.2`. Establish `hNu : IsUnit (algebraMap ℤ R (N : ℤ))` using `by simpa using hN`. Take `⟨b, -, φb, hb, -⟩` from `(hDP.1 (Sp R) (spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) hNu)) X β).exists`.

Take `⟨S, hS, hSW⟩` from `exists_span_eq_top b (fun W ↦ ∃ (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φY ∧ Nonempty Y.DetGen) (fun x ↦ by`. Take `⟨W, hW, hx, Y, φY, hY, hδ⟩` from `Obj.exists_affine_nbhd_detGen F 𝔠 M U x`. Conclude with `⟨W, ⟨hW, Y, φY, hY, hδ⟩, hx⟩)`. Establish `hloc : ∀ g : S, ∃ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left) (_ : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)) (_ : IsChartFun r₀ Y δY h) (ψ : Γ(M, W) →+* Localization.Away (g : R)) (Xg : Obj F 𝔠 (Sp (Localizati …`. Introduce `g`.

Take `⟨W, ⟨hW, Y, φY, hY, ⟨δY⟩⟩, hsub⟩` from `hSW g g.2`. Take `⟨ψ, hψ⟩` from `exists_spMap_fromSpec hW _ hsub`. Take `⟨h, hh⟩` from `H1 W hW Y φY hY δY`. Take `⟨Xg, φg, hXg⟩` from `Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away (g : R))))`. Take `⟨δg, hδg, -⟩` from `hXg.existsUnique_detGen _ δ`.

Establish `h1 : Xg.IsPullBy U (spMap ψ ≫ hW.fromSpec) (φg ≫ φb)` using `by rw [hψ]; exact hXg.comp hb`. Take `⟨χ, hχ, -⟩` from `h1.cancel hY`. Take `⟨v, hv⟩` from `presVal_exists k δY h δg hχ`. Conclude with `⟨W, hW, Y, φY, hY, δY, h, hh, ψ, Xg, φg, hXg, δg, hδg, χ, hχ, v, hv⟩`. Use `choose W hW Y φY hY δY hc hhc ψ Xg φg hXg δg hδg χ hχ vg hvg using hloc`.

Establish `side : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (ρ : R →+* T), ρ.comp (algebraMap R₀ R) = algebraMap R₀ T → ∀ (XT : Obj F 𝔠 (Sp T)) (φT : XT.A.left ⟶ X.A.left), XT.IsPullBy X (spMap ρ) φT → ∀ δT : XT.DetGen, Obj.DetCorr ρ φT δ.1 δT.1 → ∀ (g : S) (f : Localization.Away (g : R) →+* …`. Introduce `T _ _ ρ hρ XT φT hXT δT hδT g f ef`. Substitute `ef` using the available equality. Establish `hXT'` using `hXT`. Rewrite `hXT'` using `[spMap_comp]`.

Take `⟨θ, hθ, hθφ⟩` from `hXT'.cancel (hXg g)`. Establish `hd : Obj.DetCorr f θ (δg g).1 δT.1` using `detCorr_cancel (hXg g) hθ (hδg g) (hθφ ▸ hδT)`. Set `fA : Localization.Away (g : R) →ₐ[R₀] T` to `{ f with commutes' := fun r ↦ by`. Rewrite using `[IsScalarTower.algebraMap_apply R₀ R (Localization.Away (g : R)), ← hρ]`. Use `rfl }`.

Use `⟨θ ≫ χ g, by rw [spMap_comp]; exact hθ.comp (hχ g), ?_⟩` and prove the remaining obligations. Conclude with `presVal_pull (hχ g) (hvg g) fA hθ hd`. Take `⟨v, hv, huniq⟩` from `existsUnique_glue hS vg (by`. Introduce `g g' T _ f₁ f₂ e`. Use `letI : Algebra R₀ T := ((f₁.comp (algebraMap R _)).comp (algebraMap R₀ R)).toAlgebra`.

Take `⟨XT, φT, hXT⟩` from `Obj.exists_isPullBy X (spMap (f₁.comp (algebraMap R _)))`. Take `⟨δT, hδT, -⟩` from `hXT.existsUnique_detGen _ δ`. Take `⟨θ₁, hθ₁, hv₁⟩` from `side T _ rfl XT φT hXT δT hδT g f₁ rfl`. Take `⟨θ₂, hθ₂, hv₂⟩` from `side T _ rfl XT φT hXT δT hδT g' f₂ e.symm`. Conclude with `H2 (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (W g') (hW g') (Y g') (φY g') (hY g') (δY g') (hc g') (hhc g') T XT δT _ θ₁ _ θ₂ hθ₁ hθ₂ _ _ hv₁ hv₂)`.

Use `⟨v, ?_, fun v' hv' ↦ huniq v' fun g ↦ ?_⟩` and prove the remaining obligations. Introduce `R' _ _ σ X' φ' δ' hX' hδ' W' hW' Y' φY' hY' δY' h' hh' ψ' χ' hχ'`. Take `⟨w, hw⟩` from `presVal_exists k δY' h' δ' hχ'`. It suffices to establish `e : σ v = w by rw [e]; exact hw`. Establish `hS' : Ideal.span ((σ : R →+* R') '' S) = ⊤` using `by rw [← Ideal.map_span, hS, Ideal.map_top]`.

Use `eq_of_loc hS' ?_` and prove the remaining obligations. Introduce and unpack `⟨_, g, hg, rfl⟩`. Set `T` to `Localization.Away ((σ : R →+* R') g)`. Take `⟨XT, θ, hθ⟩` from `Obj.exists_isPullBy X' (spMap (algebraMap R' T))`. Take `⟨δT, hδT, -⟩` from `hθ.existsUnique_detGen _ δ'`.

Establish `e1 : IsPresVal k δY' h' δT ((algebraMap R' T).comp ψ') (θ ≫ χ') (algebraMap R' T w)` using `presVal_pull hχ' hw (IsScalarTower.toAlgHom R₀ R' T) hθ hδT`. Establish `p1 : XT.IsPullBy Y' (spMap ((algebraMap R' T).comp ψ')) (θ ≫ χ')`. Rewrite using `[spMap_comp]`. Conclude with `hθ.comp hχ'`. Establish `ef : (Localization.awayMap (σ : R →+* R') g).comp (algebraMap R _) = (algebraMap R' T).comp (σ : R →+* R')` using `IsLocalization.map_comp _`.

Take `⟨θ₁, hθ₁, hv₁⟩` from `side T ((algebraMap R' T).comp (σ : R →+* R')) (by rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, ← IsScalarTower.algebraMap_eq]) XT (θ ≫ φ') (by rw [spMap_comp]; exact hθ.comp hX') δT (detCorr_comp hX' hθ hδ' hδT) ⟨g, hg⟩ _ ef`. Establish `e2` using `H2 _ (hW _) _ _ (hY _) _ _ (hhc _) W' hW' Y' φY' hY' δY' h' hh' T XT δT _ θ₁ _ _ hθ₁ p1 _ _ hv₁ e1`. Rewrite `e2` using `[← hv ⟨g, hg⟩]`. Conclude with `(RingHom.congr_fun ef v).symm.trans e2`. Conclude with `presVal_unique k _ _ _ (hχ g) (hv' _ (IsScalarTower.toAlgHom R₀ R (Localization.Away (g : R))) (Xg g) (φg g) (δg g) (hXg g) (hδg g) (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (ψ g) (χ g) (hχ g)) (hvg g)`.
-/
theorem existsUnique_isModelVal : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
  (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k),
  (∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
    Y.IsPullBy U hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M, W), IsChartFun r₀ Y δY h) →
  (∀ (W₁ : M.Opens) (hW₁ : IsAffineOpen W₁) (Y₁ : Obj F 𝔠 (Sp Γ(M, W₁))) (φ₁ : Y₁.A.left ⟶ U.A.left),
    Y₁.IsPullBy U hW₁.fromSpec φ₁ → ∀ (δ₁ : Y₁.DetGen) (h₁ : R₀ ⊗[ℤ] Γ(M, W₁)), IsChartFun r₀ Y₁ δ₁ h₁ →
  ∀ (W₂ : M.Opens) (hW₂ : IsAffineOpen W₂) (Y₂ : Obj F 𝔠 (Sp Γ(M, W₂))) (φ₂ : Y₂.A.left ⟶ U.A.left),
    Y₂.IsPullBy U hW₂.fromSpec φ₂ → ∀ (δ₂ : Y₂.DetGen) (h₂ : R₀ ⊗[ℤ] Γ(M, W₂)), IsChartFun r₀ Y₂ δ₂ h₂ →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (ψ₁ : Γ(M, W₁) →+* R) (χ₁ : X.A.left ⟶ Y₁.A.left) (ψ₂ : Γ(M, W₂) →+* R) (χ₂ : X.A.left ⟶ Y₂.A.left),
    X.IsPullBy Y₁ (spMap ψ₁) χ₁ → X.IsPullBy Y₂ (spMap ψ₂) χ₂ →
    ∀ v₁ v₂ : R, IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁ → IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂ → v₁ = v₂) →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), levObj 𝔠 N R X → ∀ δ : X.DetGen,
    ∃! v : R, IsModelVal r₀ U X δ v := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ H1 H2 R _ _ X hlev δ
  have hN : IsUnit (N : R) := hlev.1
  obtain ⟨β⟩ := hlev.2
  have hNu : IsUnit (algebraMap ℤ R (N : ℤ)) := by simpa using hN
  obtain ⟨b, -, φb, hb, -⟩ :=
    (hDP.1 (Sp R) (spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) hNu)) X β).exists
  obtain ⟨S, hS, hSW⟩ := exists_span_eq_top b (fun W ↦ ∃ (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φY ∧ Nonempty Y.DetGen) (fun x ↦ by
    obtain ⟨W, hW, hx, Y, φY, hY, hδ⟩ := Obj.exists_affine_nbhd_detGen F 𝔠 M U x
    exact ⟨W, ⟨hW, Y, φY, hY, hδ⟩, hx⟩)

  have hloc : ∀ g : S, ∃ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left) (_ : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W))
      (_ : IsChartFun r₀ Y δY h) (ψ : Γ(M, W) →+* Localization.Away (g : R))
      (Xg : Obj F 𝔠 (Sp (Localization.Away (g : R)))) (φg : Xg.A.left ⟶ X.A.left)
      (_ : Xg.IsPullBy X (spMap (algebraMap R _)) φg) (δg : Xg.DetGen)
      (_ : Obj.DetCorr (algebraMap R _) φg δ.1 δg.1) (χ : Xg.A.left ⟶ Y.A.left)
      (_ : Xg.IsPullBy Y (spMap ψ) χ) (v : Localization.Away (g : R)), IsPresVal k δY h δg ψ χ v := by
    intro g
    obtain ⟨W, ⟨hW, Y, φY, hY, ⟨δY⟩⟩, hsub⟩ := hSW g g.2
    obtain ⟨ψ, hψ⟩ := exists_spMap_fromSpec hW _ hsub
    obtain ⟨h, hh⟩ := H1 W hW Y φY hY δY
    obtain ⟨Xg, φg, hXg⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away (g : R))))
    obtain ⟨δg, hδg, -⟩ := hXg.existsUnique_detGen _ δ
    have h1 : Xg.IsPullBy U (spMap ψ ≫ hW.fromSpec) (φg ≫ φb) := by rw [hψ]; exact hXg.comp hb
    obtain ⟨χ, hχ, -⟩ := h1.cancel hY
    obtain ⟨v, hv⟩ := presVal_exists k δY h δg hχ
    exact ⟨W, hW, Y, φY, hY, δY, h, hh, ψ, Xg, φg, hXg, δg, hδg, χ, hχ, v, hv⟩
  choose W hW Y φY hY δY hc hhc ψ Xg φg hXg δg hδg χ hχ vg hvg using hloc

  have side : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (ρ : R →+* T), ρ.comp (algebraMap R₀ R) = algebraMap R₀ T →
      ∀ (XT : Obj F 𝔠 (Sp T)) (φT : XT.A.left ⟶ X.A.left), XT.IsPullBy X (spMap ρ) φT →
      ∀ δT : XT.DetGen, Obj.DetCorr ρ φT δ.1 δT.1 →
      ∀ (g : S) (f : Localization.Away (g : R) →+* T), f.comp (algebraMap R _) = ρ →
      ∃ θ, XT.IsPullBy (Y g) (spMap (f.comp (ψ g))) θ ∧
        IsPresVal k (δY g) (hc g) δT (f.comp (ψ g)) θ (f (vg g)) := by
    intro T _ _ ρ hρ XT φT hXT δT hδT g f ef
    subst ef
    have hXT' := hXT
    rw [spMap_comp] at hXT'
    obtain ⟨θ, hθ, hθφ⟩ := hXT'.cancel (hXg g)
    have hd : Obj.DetCorr f θ (δg g).1 δT.1 := detCorr_cancel (hXg g) hθ (hδg g) (hθφ ▸ hδT)
    let fA : Localization.Away (g : R) →ₐ[R₀] T :=
      { f with
        commutes' := fun r ↦ by
          rw [IsScalarTower.algebraMap_apply R₀ R (Localization.Away (g : R)), ← hρ]
          rfl }
    refine ⟨θ ≫ χ g, by rw [spMap_comp]; exact hθ.comp (hχ g), ?_⟩
    exact presVal_pull (hχ g) (hvg g) fA hθ hd
  obtain ⟨v, hv, huniq⟩ := existsUnique_glue hS vg (by
    intro g g' T _ f₁ f₂ e
    letI : Algebra R₀ T := ((f₁.comp (algebraMap R _)).comp (algebraMap R₀ R)).toAlgebra
    obtain ⟨XT, φT, hXT⟩ := Obj.exists_isPullBy X (spMap (f₁.comp (algebraMap R _)))
    obtain ⟨δT, hδT, -⟩ := hXT.existsUnique_detGen _ δ
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T _ rfl XT φT hXT δT hδT g f₁ rfl
    obtain ⟨θ₂, hθ₂, hv₂⟩ := side T _ rfl XT φT hXT δT hδT g' f₂ e.symm
    exact H2 (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (W g') (hW g') (Y g') (φY g') (hY g')
      (δY g') (hc g') (hhc g') T XT δT _ θ₁ _ θ₂ hθ₁ hθ₂ _ _ hv₁ hv₂)
  refine ⟨v, ?_, fun v' hv' ↦ huniq v' fun g ↦ ?_⟩
  · intro R' _ _ σ X' φ' δ' hX' hδ' W' hW' Y' φY' hY' δY' h' hh' ψ' χ' hχ'
    obtain ⟨w, hw⟩ := presVal_exists k δY' h' δ' hχ'
    suffices e : σ v = w by rw [e]; exact hw
    have hS' : Ideal.span ((σ : R →+* R') '' S) = ⊤ := by rw [← Ideal.map_span, hS, Ideal.map_top]
    refine eq_of_loc hS' ?_
    rintro ⟨_, g, hg, rfl⟩
    let T := Localization.Away ((σ : R →+* R') g)
    obtain ⟨XT, θ, hθ⟩ := Obj.exists_isPullBy X' (spMap (algebraMap R' T))
    obtain ⟨δT, hδT, -⟩ := hθ.existsUnique_detGen _ δ'
    have e1 : IsPresVal k δY' h' δT ((algebraMap R' T).comp ψ') (θ ≫ χ') (algebraMap R' T w) :=
      presVal_pull hχ' hw (IsScalarTower.toAlgHom R₀ R' T) hθ hδT
    have p1 : XT.IsPullBy Y' (spMap ((algebraMap R' T).comp ψ')) (θ ≫ χ') := by
      rw [spMap_comp]; exact hθ.comp hχ'
    have ef : (Localization.awayMap (σ : R →+* R') g).comp (algebraMap R _) =
        (algebraMap R' T).comp (σ : R →+* R') := IsLocalization.map_comp _
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T ((algebraMap R' T).comp (σ : R →+* R'))
      (by rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, ← IsScalarTower.algebraMap_eq]) XT (θ ≫ φ')
      (by rw [spMap_comp]; exact hθ.comp hX') δT
      (detCorr_comp hX' hθ hδ' hδT) ⟨g, hg⟩ _ ef
    have e2 := H2 _ (hW _) _ _ (hY _) _ _ (hhc _) W' hW' Y' φY' hY' δY' h' hh' T XT δT _ θ₁ _ _ hθ₁ p1 _ _ hv₁ e1
    rw [← hv ⟨g, hg⟩] at e2
    exact (RingHom.congr_fun ef v).symm.trans e2
  · exact presVal_unique k _ _ _ (hχ g)
      (hv' _ (IsScalarTower.toAlgHom R₀ R (Localization.Away (g : R))) (Xg g) (φg g) (δg g) (hXg g) (hδg g)
        (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (ψ g) (χ g) (hχ g)) (hvg g)

end GlobalTheory.RealMult.ModelValGlue

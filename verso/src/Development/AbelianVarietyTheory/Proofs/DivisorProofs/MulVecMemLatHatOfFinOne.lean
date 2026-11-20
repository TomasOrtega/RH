import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassBotBotOfInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCompactArchimedeanMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabOfDefinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cont

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Break down `hX with h | h` into its components or cases. Rewrite using `[GlobalTheory.DefiniteCartan.eq_one_of_hasSig (h.sig w) (h.cartan w)]`. Conclude with `Commute.one_right A`. Rewrite using `[GlobalTheory.DefiniteStab.eq_neg_one_of_hasSig (h.sig w) (h.cartan w)]`. Conclude with `(Commute.one_right A).neg_right`.
-/
theorem commute_theta_of_definite {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}
    (hX : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) (w : InfinitePlace F) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute A (X.θ w) := by
  rcases hX with h | h
  · rw [GlobalTheory.DefiniteCartan.eq_one_of_hasSig (h.sig w) (h.cartan w)]
    exact Commute.one_right A
  · rw [GlobalTheory.DefiniteStab.eq_neg_one_of_hasSig (h.sig w) (h.cartan w)]
    exact (Commute.one_right A).neg_right

/- English proof (translation)
The claim follows from `(hK g).2 ⟨fun w => commute_theta_of_definite hX w _, fun z hz => ⟨h1 z hz, h2 z hz⟩⟩`.
-/
theorem mem_of_latHat {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}
    (hX : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (g : UA σ X.J)
    (h1 : ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X) (h2 : ∀ z ∈ latHat X, mat g⁻¹ *ᵥ z ∈ latHat X) : g ∈ K :=
  (hK g).2 ⟨fun w => commute_theta_of_definite hX w _, fun z hz => ⟨h1 z hz, h2 z hz⟩⟩

end GlobalTheory.DefDoubling

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hm : ((matHom (AF F) σ X.Jᵀ g).1).map (GlobalTheory.KBridge.finT F E) = 1`. Establish `h` using `congrArg Units.val (hπ g)`. Rewrite `h` using `[hg]`. Conclude with `h.symm`. Rewrite `hz`, the goal using `[GlobalTheory.KBridge.mem_latHat_iff]`.

Take `⟨hi, hf⟩` from `hz`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((GlobalTheory.KBridge.infT F E).toRingHom ∘ z) = 0` using `funext fun j => hi j`. Use `(RingHom.map_mulVec (GlobalTheory.KBridge.infT F E).toRingHom (matHom (AF F) σ X.Jᵀ g).1 z i).trans ?_` and prove the remaining obligations. Rewrite using `[e, Matrix.mulVec_zero]`.

Both sides reduce to the same expression. Establish `e : (fun i => GlobalTheory.KBridge.finT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i)) = ((matHom (AF F) σ X.Jᵀ g).1.map (GlobalTheory.KBridge.finT F E)) *ᵥ fun i => GlobalTheory.KBridge.finT F E (z i)`. Use function extensionality and compare the values at `fun i => RingHom.map_mulVec (GlobalTheory.KBridge.finT F E).toRingHom _ _ i`. Rewrite using `[e, hm, Matrix.one_mulVec]`. Conclude with `hf`.
-/
theorem mulVec_mem_latHat_of_fin_one {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n)
    {π : HA (AF F) σ X.Jᵀ →* HA (Af F) σ X.Jᵀ} (hπ : GlobalTheory.Mass.IsFinProj σ X.Jᵀ π) {g : GAd σ X.Jᵀ} (hg : π g = 1)
    {z : Fin n → AE F E} (hz : z ∈ latHat X) : (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X := by
  have hm : ((matHom (AF F) σ X.Jᵀ g).1).map (GlobalTheory.KBridge.finT F E) = 1 := by
    have h := congrArg Units.val (hπ g)
    rw [hg] at h
    exact h.symm
  rw [GlobalTheory.KBridge.mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((GlobalTheory.KBridge.infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (GlobalTheory.KBridge.infT F E).toRingHom (matHom (AF F) σ X.Jᵀ g).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => GlobalTheory.KBridge.finT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i)) =
        ((matHom (AF F) σ X.Jᵀ g).1.map (GlobalTheory.KBridge.finT F E)) *ᵥ fun i => GlobalTheory.KBridge.finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (GlobalTheory.KBridge.finT F E).toRingHom _ _ i
    rw [e, hm, Matrix.one_mulVec]
    exact hf

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm B n X hX K hK`. Choose the witnesses or unpack the hypotheses as in `⟨hL, hJ'⟩ : X.L.IsLattice E ∧ IsHermND σ X.Jᵀ := by`. Break down `hX with h | h` into its components or cases. Use `exacts [⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩, ⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩]`. Use `haveI : X.L.IsLattice E := hL`.

Use `haveI : IsTopologicalGroup (HA (AF F) σ X.Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ X.Jᵀ))`. Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj σ X.Jᵀ`. Set `e` to `GlobalTheory.IwLine.ofGAd σ X.J`. Set `K₀ : Subgroup (GAd σ X.Jᵀ)` to `K.comap e.toMonoidHom`. Establish `hmem : ∀ g : GAd σ X.Jᵀ, (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X) → (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g⁻¹).1 *ᵥ z ∈ latHat X) → g ∈ K₀`.

Introduce `g h1 h2`. Use `GlobalTheory.DefDoubling.mem_of_latHat hX hK (e g) (fun z hz => ?_) (fun z hz => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.IwLine.mat_ofGAd]`. Conclude with `h1 z hz`. Rewrite using `[← map_inv, GlobalTheory.IwLine.mat_ofGAd]`.

Conclude with `h2 z hz`. Establish `hlev : levelOpen σ X.Jᵀ X.L ≤ K₀` using `fun g hg => hmem g (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg hg hz) (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg (inv_mem hg) hz)`. Establish `hK₀ : IsOpen (K₀ : Set (GAd σ X.Jᵀ))` using `Subgroup.isOpen_mono hlev (isOpen_levelOpen σ X.Jᵀ X.L)`. Establish `hker : ∀ g, π g = 1 → g ∈ K₀` using `fun g hg => hmem g (fun z hz => mulVec_mem_latHat_of_fin_one X hπ hg hz) (fun z hz => mulVec_mem_latHat_of_fin_one X hπ (by rw [map_inv, hg, inv_one]) hz)`. Establish `hback : ∀ g, π g ∈ K₀.map π → g ∈ K₀`.

Introduce and unpack `g ⟨k, hk, hkg⟩`. Establish `h : k⁻¹ * g ∈ K₀` using `hker _ (by rw [map_mul, map_inv, hkg, inv_mul_cancel])`. Simplify using `using K₀.mul_mem hk h`. Establish `hK' : IsOpen ((K₀.map π : Subgroup (HA (Af F) σ X.Jᵀ)) : Set (HA (Af F) σ X.Jᵀ))` using `GlobalTheory.Mass.Model.isOpen_of_comap hπ (Subgroup.isOpen_mono (Subgroup.le_comap_map π K₀) hK₀)`. Take `⟨S, hS⟩` from `GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm n X.Jᵀ hJ' _ hK'`.

Take `⟨sec, -, hsec⟩` from `GlobalTheory.Mass.Model.exists_section hπ`. Use `⟨S.image (fun s => e (sec s)), fun x => ?_⟩` and prove the remaining obligations. Take `⟨γ, s, hs, k, hk, hx⟩` from `hS (π (e.symm x))`. Establish `hγ : (γ.1 : HA (Af F) σ X.Jᵀ) ∈ (GlobalTheory.Mass.ratIn (AF F) σ X.Jᵀ).map π`. Rewrite using `[hπ.map_ratIn]`.

Conclude with `γ.2`. Take `⟨γ₀, hγ₀, hγπ⟩` from `hγ`. Establish `hw : (γ₀ * sec s)⁻¹ * e.symm x ∈ K₀`. Use `hback _ ?_` and prove the remaining obligations. Set `γ' : HA (Af F) σ X.Jᵀ` to `γ.1`.

Establish `hx' : π (e.symm x) = γ' * (s * k)` using `hx`. Rewrite using `[map_mul, map_inv, map_mul, hγπ, hsec, hx', show (γ' * s)⁻¹ * (γ' * (s * k)) = k by group]`. Conclude with `hk`. Use `⟨e (sec s), Finset.mem_image_of_mem _ hs, e γ₀, ?_, e ((γ₀ * sec s)⁻¹ * e.symm x), hw, ?_⟩` and prove the remaining obligations. Take `⟨u, -, hu⟩` from `hγ₀`.

Conclude with `⟨u, hu⟩`. Rewrite using `[← map_mul, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul, MulEquiv.apply_symm_apply]`.
-/
theorem exists_finite_doubleCosets : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {B : Base F E} {n : ℕ} {X : Spc F E n},
    (X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) → ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∃ A : Finset (UA σ X.J), ∀ x, ∃ a ∈ A, ∃ γ ∈ ratU σ X.J, ∃ k ∈ K, x = γ * a * k := by
  intro F E _ _ _ _ _ σ hcm B n X hX K hK
  classical
  obtain ⟨hL, hJ'⟩ : X.L.IsLattice E ∧ IsHermND σ X.Jᵀ := by
    rcases hX with h | h
    exacts [⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩, ⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩]
  haveI : X.L.IsLattice E := hL
  haveI : IsTopologicalGroup (HA (AF F) σ X.Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ X.Jᵀ))
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ X.Jᵀ
  let e := GlobalTheory.IwLine.ofGAd σ X.J
  let K₀ : Subgroup (GAd σ X.Jᵀ) := K.comap e.toMonoidHom
  have hmem : ∀ g : GAd σ X.Jᵀ, (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X) →
      (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g⁻¹).1 *ᵥ z ∈ latHat X) → g ∈ K₀ := by
    intro g h1 h2
    refine GlobalTheory.DefDoubling.mem_of_latHat hX hK (e g) (fun z hz => ?_) (fun z hz => ?_)
    · rw [GlobalTheory.IwLine.mat_ofGAd]; exact h1 z hz
    · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]; exact h2 z hz
  have hlev : levelOpen σ X.Jᵀ X.L ≤ K₀ := fun g hg =>
    hmem g (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg hg hz)
      (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg (inv_mem hg) hz)
  have hK₀ : IsOpen (K₀ : Set (GAd σ X.Jᵀ)) := Subgroup.isOpen_mono hlev (isOpen_levelOpen σ X.Jᵀ X.L)
  have hker : ∀ g, π g = 1 → g ∈ K₀ := fun g hg =>
    hmem g (fun z hz => mulVec_mem_latHat_of_fin_one X hπ hg hz)
      (fun z hz => mulVec_mem_latHat_of_fin_one X hπ (by rw [map_inv, hg, inv_one]) hz)
  have hback : ∀ g, π g ∈ K₀.map π → g ∈ K₀ := by
    rintro g ⟨k, hk, hkg⟩
    have h : k⁻¹ * g ∈ K₀ := hker _ (by rw [map_mul, map_inv, hkg, inv_mul_cancel])
    simpa using K₀.mul_mem hk h
  have hK' : IsOpen ((K₀.map π : Subgroup (HA (Af F) σ X.Jᵀ)) : Set (HA (Af F) σ X.Jᵀ)) :=
    GlobalTheory.Mass.Model.isOpen_of_comap hπ (Subgroup.isOpen_mono (Subgroup.le_comap_map π K₀) hK₀)
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm n X.Jᵀ hJ' _ hK'
  obtain ⟨sec, -, hsec⟩ := GlobalTheory.Mass.Model.exists_section hπ
  refine ⟨S.image (fun s => e (sec s)), fun x => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS (π (e.symm x))
  have hγ : (γ.1 : HA (Af F) σ X.Jᵀ) ∈ (GlobalTheory.Mass.ratIn (AF F) σ X.Jᵀ).map π := by
    rw [hπ.map_ratIn]; exact γ.2
  obtain ⟨γ₀, hγ₀, hγπ⟩ := hγ
  have hw : (γ₀ * sec s)⁻¹ * e.symm x ∈ K₀ := by
    refine hback _ ?_
    let γ' : HA (Af F) σ X.Jᵀ := γ.1
    have hx' : π (e.symm x) = γ' * (s * k) := hx
    rw [map_mul, map_inv, map_mul, hγπ, hsec, hx', show (γ' * s)⁻¹ * (γ' * (s * k)) = k by group]
    exact hk
  refine ⟨e (sec s), Finset.mem_image_of_mem _ hs, e γ₀, ?_, e ((γ₀ * sec s)⁻¹ * e.symm x), hw, ?_⟩
  · obtain ⟨u, -, hu⟩ := hγ₀
    exact ⟨u, hu⟩
  · rw [← map_mul, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.DefDoubling

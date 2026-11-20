import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

namespace GlobalTheory.CompanionTheory.RedCov.MahlerU

/- English proof (translation)
Take `⟨C, hC, hC'⟩` from `Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε`. Set `Lm : m → Matrix (Fin n) (Fin n) 𝔸[K]` to `fun k => (L k).map (algebraMap K 𝔸[K])`. Set `Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K]` to `fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k * ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])`. Establish `hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L`. Introduce `g g'`.

Rewrite using `[funext_iff]`. Conclude with `forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)`. Establish `hΦc : Continuous Φ` using `continuous_pi fun k => ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)`. Set `ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K]` to `fun r k => (r k).map (algebraMap K 𝔸[K])`. Establish `hψfin : {r | ψ r ∈ Φ '' C}.Finite`.

Use `finite_of_isCompact_coords (hC.image hΦc) ψ (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2) (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2) (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)` and prove the remaining obligations. Introduce `r r' h`. Use function extensionality and compare the values at `k i j`. Conclude with `congrFun h (k, i, j)`. Establish `hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite`.

Use `(hψfin.image ψ).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩`. Establish `e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k * ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Use function extensionality and compare the values at `k`. Simplify using `only [ψ, Φ, Lm, ← map_inv]`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Rewrite `hC1`, the goal using `[e]`. Conclude with `⟨_, hC1, rfl⟩`. Take `⟨T, hTΓ, hT⟩` from `exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n) hΦ C hfin`.

Use `⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C, T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩` from `hC' g (hG1 g hg) (hh g hg)`. Take `⟨δ, hδT, hγδ, hδc⟩` from `hT g (hGL g hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm`. Take `⟨δ₀, rfl⟩` from `hTΓ δ hδT`.

Use `⟨γ₀ * δ₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← diagonal_mem_adelicCentralizer_iff, map_mul]`. Conclude with `hγδ`. Use `Set.mem_biUnion hδT ⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.
-/
theorem exists_isCompact_centralizer_reduction_set {K : Type*} [Field K] [NumberField K] {n : ℕ} {m : Type*}
    [Finite m] (L : m → Matrix (Fin n) (Fin n) K)
    (G : Set (AdelicGLn.AdelicGL K n)) (hG1 : ∀ g ∈ G, g ∈ Reduction.normOneGL K n)
    (hGL : ∀ g ∈ G, g ∈ adelicCentralizer L) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G, ∀ x : Fin n → K, x ≠ 0 → ε ≤ Reduction.height g x) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ G, ∃ γ : GL (Fin n) K,
      (∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ) ∧
        (AdelicGLn.diagonal K n γ)⁻¹ * g ∈ C := by
  classical
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
  let Lm : m → Matrix (Fin n) (Fin n) 𝔸[K] := fun k => (L k).map (algebraMap K 𝔸[K])
  let Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k *
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L := by
    intro g g'
    rw [funext_iff]
    exact forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)
  have hΦc : Continuous Φ := continuous_pi fun k =>
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)
  let ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun r k => (r k).map (algebraMap K 𝔸[K])
  have hψfin : {r | ψ r ∈ Φ '' C}.Finite := by
    refine finite_of_isCompact_coords (hC.image hΦc) ψ
      (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2)
      (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2)
      (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)
    intro r r' h
    funext k i j
    exact congrFun h (k, i, j)
  have hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite := by
    refine (hψfin.image ψ).subset ?_
    rintro _ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩
    have e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k *
        ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      funext k
      simp only [ψ, Φ, Lm, ← map_inv]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e] at hC1 ⊢
    exact ⟨_, hC1, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n)
    hΦ C hfin
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro g hg
  obtain ⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩ := hC' g (hG1 g hg) (hh g hg)
  obtain ⟨δ, hδT, hγδ, hδc⟩ := hT g (hGL g hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm
  obtain ⟨δ₀, rfl⟩ := hTΓ δ hδT
  refine ⟨γ₀ * δ₀, ?_, ?_⟩
  · rw [← diagonal_mem_adelicCentralizer_iff, map_mul]
    exact hγδ
  · refine Set.mem_biUnion hδT ⟨c, hc, ?_⟩
    rw [map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

section Unitary

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

local notation "𝒩'" => Fintype.card (ι × Fin (Module.finrank K E))

variable [NumberField K]

/- English proof (translation)
Set `G : Set (AdelicGLn.AdelicGL K (Fintype.card (ι × Fin d)))` to `(fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) '' Y`. Establish `hG1 : ∀ g ∈ G, g ∈ Reduction.normOneGL K (Fintype.card (ι × Fin d))`. Introduce and unpack `_ ⟨u, -, rfl⟩`. Rewrite using `[Reduction.mem_normOneGL]`. Use `set a := AdelicGLn.det K (Fintype.card (ι × Fin d)) (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)))`.

Establish `ha : a * a = 1`. Use `ext`. Simplify `det_trHom_mul_self b 𝔸[K] H hH u` using `[a]`. Establish `h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) * (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1`. Establish `h3` using `congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha`.

Rewrite `h3` using `[map_mul, map_one]`. Simplify using `using congrArg Subtype.val h3`. Establish `hpos` using `(GroundTheory.Global.IdeleGroup.ideleModule K a).2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hGL : ∀ g ∈ G, g ∈ adelicCentralizer (resScalar (ι` using `ι) b) := by`.

Introduce and unpack `_ ⟨u, -, rfl⟩ j`. Establish `e` using `resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j`. Express the relevant statement in the definitionally equal form `_ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) = (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _`. Rewrite using `[e]`. Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype]`.

Rewrite using `[trHom_val]`. Conclude with `resHom_commute_scalar b 𝔸[K] _ _`. Take `⟨C, hC, hred⟩` from `exists_isCompact_centralizer_reduction_set (resScalar (ι := ι) b) G hG1 hGL hε (by rintro _ ⟨u, hu, rfl⟩ x hx; exact hh u hu x hx)`. Use `⟨C, hC, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγC⟩` from `hred _ ⟨u, hu, rfl⟩`.

Take `⟨M, hM⟩` from `exists_resHom_eq_of_commute b γ hγ`. Use `⟨inside₂ (K ⊗[K] E) M, ?_⟩` and prove the remaining obligations. Establish `e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) = AdelicGLn.diagonal K (Fintype.card (ι × Fin d)) γ`. Use extensionality with `: 1`. Rewrite using `[← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]`.

Both sides reduce to the same expression. Rewrite using `[map_mul, map_inv, e]`. Conclude with `hγC`.
-/
theorem exists_isCompact_trHom_set {d : ℕ} (b : Module.Basis (Fin d) K E) (hH : IsUnit H.det)
    (Y : Set (unitaryPoints K E H 𝔸[K])) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ u ∈ Y, ∀ x : Fin (Fintype.card (ι × Fin d)) → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x) :
    ∃ C : Set (GL (Fin (Fintype.card (ι × Fin d))) 𝔸[K]), IsCompact C ∧ ∀ u ∈ Y,
      ∃ M : GL ι (K ⊗[K] E), trHom b 𝔸[K]
        ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) ∈ C := by
  classical
  let G : Set (AdelicGLn.AdelicGL K (Fintype.card (ι × Fin d))) :=
    (fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) '' Y
  have hG1 : ∀ g ∈ G, g ∈ Reduction.normOneGL K (Fintype.card (ι × Fin d)) := by
    rintro _ ⟨u, -, rfl⟩
    rw [Reduction.mem_normOneGL]
    set a := AdelicGLn.det K (Fintype.card (ι × Fin d)) (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)))
    have ha : a * a = 1 := by
      ext
      simpa [a] using det_trHom_mul_self b 𝔸[K] H hH u
    have h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) *
        (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1 := by
      have h3 := congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha
      rw [map_mul, map_one] at h3
      simpa using congrArg Subtype.val h3
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule K a).2
    nlinarith
  have hGL : ∀ g ∈ G, g ∈ adelicCentralizer (resScalar (ι := ι) b) := by
    rintro _ ⟨u, -, rfl⟩ j
    have e := resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j
    change _ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) =
      (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _
    rw [e]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [trHom_val]
    exact resHom_commute_scalar b 𝔸[K] _ _
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction_set (resScalar (ι := ι) b) G hG1 hGL hε
    (by rintro _ ⟨u, hu, rfl⟩ x hx; exact hh u hu x hx)
  refine ⟨C, hC, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨u, hu, rfl⟩
  obtain ⟨M, hM⟩ := exists_resHom_eq_of_commute b γ hγ
  refine ⟨inside₂ (K ⊗[K] E) M, ?_⟩
  have e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) =
      AdelicGLn.diagonal K (Fintype.card (ι × Fin d)) γ := by
    ext : 1
    rw [← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]
    rfl
  rw [map_mul, map_inv, e]
  exact hγC

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Take `⟨C, hC, hred⟩` from `exists_isCompact_trHom_set H b hH Y hε hh`. Use `set α := Algebra.ofId K 𝔸[K] with hα`. Use `set Hb := baseMatrix K H 𝔸[K] with hHb`. Set `Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun x => cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x`.

Set `Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun g => Ψ g⁻¹`. Establish `hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y`. Introduce `x y`. Simplify using `only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]`. Establish `hΨone : Ψ 1 = Hb`.

Simplify using `[Ψ, cstar_one]`. Establish `hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)), cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X`. Introduce `z X`. Establish `h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1`. Rewrite using `[← cstar_mul, z.inv_mul, cstar_one]`.

Establish `h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1` using `z.inv_mul`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]`. Establish `hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K]`.

Introduce `g g'`. Establish `e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g⁻¹ = _`. Rewrite using `[← hΨmul, mul_inv_cancel_right]`. Establish `e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g'⁻¹ = _`. Rewrite using `[← hΨone, ← hΨmul, one_mul]`.

Rewrite using `[e1, e2]`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Establish `h` using `congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he`. Simplify using `only [hcancel] at h`.

Conclude with `h`. Introduce `hu`. Establish `h : Ψ (g⁻¹ * g') = Hb` using `hu`. Rewrite using `[h]`. Set `Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E))` to `(diagGL (ι := ι) α).range`.

Set `C₂ : Set (GL ι (𝔸[K] ⊗[K] E))` to `{w | trHom b 𝔸[K] w ∈ C}`. Set `Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun A => cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ`. Establish `hΨ'c : Continuous Ψ'`. Establish `h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := (continuous_readoff b 𝔸[K]).matrix_transpose`. Establish `h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => cstar (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := by show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ`.

Conclude with `(h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose`. Conclude with `(h2.matrix_mul continuous_const).matrix_mul h1`. Establish `hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])`. Introduce `w _`. Use `show Ψ w⁻¹ = _`.

Simplify using `only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]`. Establish `hX : IsCompact (Ψ' '' (Units.val '' C))` using `(hC.image Units.continuous_val).image hΨ'c`. Set `ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun V => V.map (baseMap α)`. Establish `hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) = ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)))`. Introduce `M`.

Use `show Ψ (diagGL α M)⁻¹ = _`. Rewrite using `[← map_inv]`. Simplify using `only [Ψ, ψ, diagGL_val]`. Rewrite using `[cstar_mul_baseMatrix_map]`. Establish `hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite`.

Use `finite_of_isCompact_coords hX ψ (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2) (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (continuous_id.matrix_elem _ _))) (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_` and prove the remaining obligations. Introduce `V V' h`. Use extensionality with `i j`. Apply `(coords b K).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Conclude with `congrFun h (i, j, k)`. Introduce `V p`. Simplify using `only [ψ, Matrix.map_apply, coords_baseMap]`. Both sides reduce to the same expression. Establish `hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite`.

Use `(hfinV.image ψ).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩`. Use `⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩` and prove the remaining obligations. Use `show ψ _ ∈ Ψ' '' (Units.val '' C)`. Rewrite using `[← hΓ M, he, hC₂ w hw]`.

Conclude with `⟨_, ⟨_, hw, rfl⟩, rfl⟩`. Rewrite using `[← hΓ M, he]`. Take `⟨T, hTΓ, hT⟩` from `exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin`. Set `C₃ : Set (GL (Fin 𝒩') 𝔸[K])` to `⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C`. Establish `hC₃ : IsCompact C₃` using `T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)`.

Set `Ω : Set (unitaryPoints K E H 𝔸[K])` to `{v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}`. Use `⟨Ω, ?_, ?_⟩` and prove the remaining obligations. Establish `hΩcl : IsClosed Ω` using `hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)`. Set `F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K]` to `fun A p => coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2`. Establish `hFc : Continuous F` using `continuous_pi fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))`.

Use `set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD`. Establish `hDc : IsCompact D` using `(isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage ((hC₃.image Units.continuous_val).image hFc)`. Establish `hsub : Ω ⊆ D⁻¹`. Introduce `v hv`. Use `show v⁻¹ ∈ D`.

Use `⟨_, ⟨_, hv, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `only [F, trHom_val, readoff_resHom, transpose_transpose]`. Both sides reduce to the same expression. Conclude with `hDc.inv.of_isClosed_subset hΩcl hsub`.

Introduce `u huY`. Take `⟨M, hM⟩` from `hred u huY`. Take `⟨δ, hδT, hηδ, -⟩` from `hT u u.2 (diagGL α M) ⟨M, rfl⟩ ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])`. Take `⟨m, rfl⟩` from `hTΓ δ hδT`. Rewrite `hηδ` using `[← map_mul]`.

Establish `hU` using `mem_unitaryPoints_of_diagGL H hηδ`. Use `⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) : GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m)` using `Units.ext rfl`. Use `show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, e]`.

Use `Set.mem_biUnion hδT ⟨_, hM, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]`.
-/
theorem exists_isCompact_unitary_set (hH : IsUnit H.det)
    (Y : Set (unitaryPoints K E H 𝔸[K])) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ u ∈ Y, ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom (Module.finBasis K E) 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x) :
    ∃ Ω : Set (unitaryPoints K E H 𝔸[K]), IsCompact Ω ∧ ∀ u ∈ Y,
      ∃ θ ∈ (unitaryDiagonal K H).range, θ⁻¹ * u ∈ Ω := by
  classical
  let b := Module.finBasis K E
  obtain ⟨C, hC, hred⟩ := exists_isCompact_trHom_set H b hH Y hε hh
  set α := Algebra.ofId K 𝔸[K] with hα
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun x =>
    cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x
  let Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun g => Ψ g⁻¹
  have hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y := by
    intro x y
    simp only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]
  have hΨone : Ψ 1 = Hb := by
    simp [Ψ, cstar_one]
  have hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)),
      cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
          ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X := by
    intro z X
    have h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := by
      rw [← cstar_mul, z.inv_mul, cstar_one]
    have h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := z.inv_mul
    calc _ = (cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
          cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * X *
          (((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
            (z : Matrix ι ι (𝔸[K] ⊗[K] E))) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K] := by
    intro g g'
    have e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g⁻¹ = _
      rw [← hΨmul, mul_inv_cancel_right]
    have e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g'⁻¹ = _
      rw [← hΨone, ← hΨmul, one_mul]
    rw [e1, e2]
    constructor
    · intro he
      have h := congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
        (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he
      simp only [hcancel] at h
      exact h
    · intro hu
      have h : Ψ (g⁻¹ * g') = Hb := hu
      rw [h]
  let Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E)) := (diagGL (ι := ι) α).range
  let C₂ : Set (GL ι (𝔸[K] ⊗[K] E)) := {w | trHom b 𝔸[K] w ∈ C}
  let Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E) := fun A =>
    cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ
  have hΨ'c : Continuous Ψ' := by
    have h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι := ι) b 𝔸[K] A)ᵀ :=
      (continuous_readoff b 𝔸[K]).matrix_transpose
    have h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        cstar (readoff (ι := ι) b 𝔸[K] A)ᵀ := by
      show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ
      exact (h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose
    exact (h2.matrix_mul continuous_const).matrix_mul h1
  have hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K]) := by
    intro w _
    show Ψ w⁻¹ = _
    simp only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]
  have hX : IsCompact (Ψ' '' (Units.val '' C)) := (hC.image Units.continuous_val).image hΨ'c
  let ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun V => V.map (baseMap α)
  have hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) =
      ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))) := by
    intro M
    show Ψ (diagGL α M)⁻¹ = _
    rw [← map_inv]
    simp only [Ψ, ψ, diagGL_val]
    rw [cstar_mul_baseMatrix_map]
  have hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite := by
    refine finite_of_isCompact_coords hX ψ
      (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2)
      (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp
        (continuous_id.matrix_elem _ _)))
      (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_
    · intro V V' h
      ext i j
      apply (coords b K).injective
      funext k
      exact congrFun h (i, j, k)
    · intro V p
      simp only [ψ, Matrix.map_apply, coords_baseMap]
      rfl
  have hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite := by
    refine (hfinV.image ψ).subset ?_
    rintro _ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩
    refine ⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩
    · show ψ _ ∈ Ψ' '' (Units.val '' C)
      rw [← hΓ M, he, hC₂ w hw]
      exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
    · rw [← hΓ M, he]
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin
  let C₃ : Set (GL (Fin 𝒩') 𝔸[K]) := ⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C
  have hC₃ : IsCompact C₃ :=
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)
  let Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}
  refine ⟨Ω, ?_, ?_⟩
  · have hΩcl : IsClosed Ω :=
      hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)
    let F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K] :=
      fun A p =>
      coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2
    have hFc : Continuous F := continuous_pi fun p => (continuous_apply _).comp
      ((continuous_coords b 𝔸[K]).comp
        (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))
    set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD
    have hDc : IsCompact D := (isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage
      ((hC₃.image Units.continuous_val).image hFc)
    have hsub : Ω ⊆ D⁻¹ := by
      intro v hv
      show v⁻¹ ∈ D
      refine ⟨_, ⟨_, hv, rfl⟩, ?_⟩
      funext p
      simp only [F, trHom_val, readoff_resHom, transpose_transpose]
      rfl
    exact hDc.inv.of_isClosed_subset hΩcl hsub
  · intro u huY
    obtain ⟨M, hM⟩ := hred u huY
    obtain ⟨δ, hδT, hηδ, -⟩ := hT u u.2 (diagGL α M) ⟨M, rfl⟩
      ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])
    obtain ⟨m, rfl⟩ := hTΓ δ hδT
    rw [← map_mul] at hηδ
    have hU := mem_unitaryPoints_of_diagGL H hηδ
    refine ⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩
    have e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) :
        GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m) := Units.ext rfl
    show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) :
      GL ι (𝔸[K] ⊗[K] E)) ∈ C₃
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    refine Set.mem_biUnion hδT ⟨_, hM, ?_⟩
    simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]

end Unitary

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ n H hH Y ε hε hh`. Conclude with `exists_isCompact_unitary_set H hH Y hε hh`.
-/
theorem mahler_unitary_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω := by
  intro F E _ _ _ _ _ _ n H hH Y ε hε hh
  exact exists_isCompact_unitary_set H hH Y hε hh

end GlobalTheory.CompanionTheory.RedCov.MahlerU

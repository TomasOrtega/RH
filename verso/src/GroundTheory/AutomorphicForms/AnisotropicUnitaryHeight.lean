import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
import GroundTheory.AutomorphicForms.AnisotropicHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

local notation "𝒩" => Fintype.card (ι × κ)

section Algebraic

variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem baseMap_eq_tensorMap (f : R →ₐ[K] R') :
    (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E) = tensorMap E f := rfl

variable {R}

/- English proof (translation)
Rewrite using `[baseMap_eq_tensorMap]`. Unfold `hermValue`. Express the relevant statement in the definitionally equal form `(tensorMap E f : R ⊗[K] E →+* R' ⊗[K] E) (_ ⬝ᵥ _) = _`. Rewrite using `[RingHom.map_dotProduct]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[tensorMap_conjBase]`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, RingHom.map_mulVec]`. Use `congr 1`.

Use extensionality with `a c`. Simplify using `[baseMatrix]`.
-/
theorem hermValue_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    baseMap f (hermValue K H R x) = hermValue K H R' (fun i => baseMap f (x i)) := by
  rw [baseMap_eq_tensorMap]
  unfold hermValue
  change (tensorMap E f : R ⊗[K] E →+* R' ⊗[K] E) (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  congr 1
  · funext i
    simp [tensorMap_conjBase]
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a c
    simp [baseMatrix]

variable (R)

def hermCoords (y : Fin 𝒩 → R) : κ → R := coords b R (hermValue K H R (ofResVec b R y))

/- English proof (translation)
Rewrite using `[hermCoords, ofResVec_smul, hermValue_smul, map_smul, sq]`. Both sides reduce to the same expression.
-/
theorem hermCoords_smul (t : R) (y : Fin 𝒩 → R) :
    hermCoords H b R (t • y) = t ^ 2 • hermCoords H b R y := by
  rw [hermCoords, ofResVec_smul, hermValue_smul, map_smul, sq]
  rfl

variable {R}

/- English proof (translation)
Apply `resVec_injective b R'` to reduce the goal to its premises. Rewrite using `[resVec_ofResVec, resVec_baseMap, resVec_ofResVec]`.
-/
theorem ofResVec_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    ofResVec b R' (f ∘ y) = fun i => baseMap f (ofResVec b R y i) := by
  apply resVec_injective b R'
  rw [resVec_ofResVec, resVec_baseMap, resVec_ofResVec]

/- English proof (translation)
Rewrite using `[hermCoords, ofResVec_comp, ← hermValue_baseMap, coords_baseMap]`. Both sides reduce to the same expression.
-/
theorem hermCoords_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    hermCoords H b R' (f ∘ y) = f ∘ hermCoords H b R y := by
  rw [hermCoords, ofResVec_comp, ← hermValue_baseMap, coords_baseMap]
  rfl

def hermPoly (k : κ) : MvPolynomial (Fin 𝒩) K :=
  hermCoords H b (MvPolynomial (Fin 𝒩) K) MvPolynomial.X k

/- English proof (translation)
Establish `h` using `congrFun (hermCoords_comp H b (MvPolynomial.aeval y) MvPolynomial.X) k`. Establish `hy : (MvPolynomial.aeval y : MvPolynomial (Fin 𝒩) K →ₐ[K] R) ∘ MvPolynomial.X = y`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Rewrite `h` using `[hy]`.

Conclude with `h.symm`.
-/
theorem aeval_hermPoly (y : Fin 𝒩 → R) (k : κ) :
    MvPolynomial.aeval y (hermPoly H b k) = hermCoords H b R y k := by
  have h := congrFun (hermCoords_comp H b (MvPolynomial.aeval y) MvPolynomial.X) k
  have hy : (MvPolynomial.aeval y : MvPolynomial (Fin 𝒩) K →ₐ[K] R) ∘ MvPolynomial.X = y := by
    funext p
    simp
  rw [hy] at h
  exact h.symm

def inside₂ (S : Type*) [CommRing S] : GL ι S →* GL ι S where
  toFun g := ⟨(↑g⁻¹ : Matrix ι ι S)ᵀ, (g : Matrix ι ι S)ᵀ,
    by rw [← transpose_mul, g.mul_inv, transpose_one],
    by rw [← transpose_mul, g.inv_mul, transpose_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' g h := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul]

/- English proof (translation)
Rewrite using `[trHom_val]`. Use `congr 1`.
-/
theorem trHom_invTr (g : GL ι (R ⊗[K] E)) :
    (trHom b R (inside₂ (R ⊗[K] E) g) : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ↑g := by
  rw [trHom_val]
  congr 1

def diagGL (f : R →ₐ[K] R') : GL ι (R ⊗[K] E) →* GL ι (R' ⊗[K] E) :=
  Units.map ((AlgHom.mapMatrix (baseMap f) : Matrix ι ι (R ⊗[K] E) →ₐ[K] Matrix ι ι (R' ⊗[K] E)).toRingHom.toMonoidHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagGL_val (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    (diagGL f g : Matrix ι ι (R' ⊗[K] E)) = (g : Matrix ι ι (R ⊗[K] E)).map (baseMap f) := rfl

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `only [diagGL_val]`. Use `show ((↑(diagGL f g)⁻¹ : Matrix ι ι (R' ⊗[K] E)))ᵀ = ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ).map _`. Rewrite using `[← map_inv, diagGL_val, transpose_map]`.
-/
theorem invTr_diagGL (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    inside₂ (R' ⊗[K] E) (diagGL f g) = diagGL f (inside₂ (R ⊗[K] E) g) := by
  ext : 1
  simp only [diagGL_val]
  show ((↑(diagGL f g)⁻¹ : Matrix ι ι (R' ⊗[K] E)))ᵀ = ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ).map _
  rw [← map_inv, diagGL_val, transpose_map]

end Algebraic

section Heights

variable [NumberField K] {d : ℕ} (b : Basis (Fin d) K E)

local notation "𝒩'" => Fintype.card (ι × Fin d)

/- English proof (translation)
Establish `hx : Reduction.ratVec x = resVec b 𝔸[K] (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i))`. Rewrite using `[resVec_baseMap, resVec_ofResVec]`. Both sides reduce to the same expression. Rewrite using `[hx, resVec_vecMul_trHom, hermCoords, ofResVec_resVec]`. Establish `h` using `hermValue_mulVec (K := K) (H := H) (u⁻¹) (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i))`.

Rewrite `h` using `[show unitaryMat (u⁻¹) = (↑(u : GL ι (𝔸[K] ⊗[K] E))⁻¹ : Matrix ι ι (𝔸[K] ⊗[K] E)) from rfl]`. Rewrite using `[h, ← hermValue_baseMap, coords_baseMap]`. Both sides reduce to the same expression.
-/
theorem hermCoords_vecMul_trHom (x : Fin 𝒩' → K) (u : unitaryPoints K E H 𝔸[K]) :
    hermCoords H b 𝔸[K] (Reduction.ratVec x ᵥ* (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)) :
      Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])) = Reduction.ratVec (hermCoords H b K x) := by
  have hx : Reduction.ratVec x = resVec b 𝔸[K]
      (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i)) := by
    rw [resVec_baseMap, resVec_ofResVec]
    rfl
  rw [hx, resVec_vecMul_trHom, hermCoords, ofResVec_resVec]
  have h := hermValue_mulVec (K := K) (H := H) (u⁻¹)
    (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i))
  rw [show unitaryMat (u⁻¹) = (↑(u : GL ι (𝔸[K] ⊗[K] E))⁻¹ : Matrix ι ι (𝔸[K] ⊗[K] E)) from rfl]
    at h
  rw [h, ← hermValue_baseMap, coords_baseMap]
  rfl

/- English proof (translation)
Take `⟨C, hC, hCb⟩` from `exists_adelicNorm_aeval_le (K := K) (d := 2) two_pos (hermPoly H b) (fun v t y k => by`. Rewrite using `[aeval_hermPoly, aeval_hermPoly, hermCoords_smul]`. Use the proof step `rfl)`. Use the proof step `(fun w t y k => by`. Rewrite using `[aeval_hermPoly, aeval_hermPoly, hermCoords_smul]`.

Use the proof step `rfl)`. Establish `hG : ∀ g ∈ Set.range fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)), ∀ x : Fin 𝒩' → K, x ≠ 0 → ∃ s : GroundTheory.Global.IdeleGroup K, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) ∧ ∃ z : Fin d → K, z ≠ 0 ∧ (fun y k => MvPolynomial.aeval y ( …`. Introduce and unpack `_ ⟨u, rfl⟩ x hx`. Use `⟨1, by simp, hermCoords H b K x, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Establish `h1 : hermValue K H K (ofResVec b K x) = 0`. Apply `(coords b K).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h0`.

Establish `h2` using `haniso _ h1`. Rewrite using `[← resVec_ofResVec b K x, h2]`. Use function extensionality and compare the values at `p`. Simplify using `[resVec, coordsVec]`. Use function extensionality and compare the values at `k`.

Simplify using `only [aeval_hermPoly, Units.val_one, one_smul]`. Rewrite using `[hermCoords_vecMul_trHom]`. Take `⟨ε, hε, h⟩` from `exists_pos_le_height_of_bound (Set.range fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) (fun y k => MvPolynomial.aeval y (hermPoly H b k)) hC two_pos hCb hG`. Conclude with `⟨ε, hε, fun u x hx => h _ ⟨u, rfl⟩ x hx⟩`.
-/
theorem exists_pos_le_height_trHom
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : unitaryPoints K E H 𝔸[K], ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := K) (d := 2) two_pos (hermPoly H b)
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  have hG : ∀ g ∈ Set.range fun u : unitaryPoints K E H 𝔸[K] =>
      trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)), ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ∃ s : GroundTheory.Global.IdeleGroup K, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) ∧
        ∃ z : Fin d → K, z ≠ 0 ∧ (fun y k => MvPolynomial.aeval y (hermPoly H b k))
          (Reduction.ratVec x ᵥ* (g : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])) =
            (s : 𝔸[K]) • Reduction.ratVec z := by
    rintro _ ⟨u, rfl⟩ x hx
    refine ⟨1, by simp, hermCoords H b K x, ?_, ?_⟩
    · intro h0
      apply hx
      have h1 : hermValue K H K (ofResVec b K x) = 0 := by
        apply (coords b K).injective
        rw [map_zero]
        exact h0
      have h2 := haniso _ h1
      rw [← resVec_ofResVec b K x, h2]
      funext p
      simp [resVec, coordsVec]
    · funext k
      simp only [aeval_hermPoly, Units.val_one, one_smul]
      rw [hermCoords_vecMul_trHom]
  obtain ⟨ε, hε, h⟩ := exists_pos_le_height_of_bound
    (Set.range fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)))
    (fun y k => MvPolynomial.aeval y (hermPoly H b k)) hC two_pos hCb hG
  exact ⟨ε, hε, fun u x hx => h _ ⟨u, rfl⟩ x hx⟩

/- English proof (translation)
Take `⟨ε, hε, hh⟩` from `exists_pos_le_height_trHom H b haniso`. Set `G : Subgroup (AdelicGLn.AdelicGL K 𝒩')` to `((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype).range`. Establish `hG1 : G ≤ Reduction.normOneGL K 𝒩'`. Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[Reduction.mem_normOneGL]`.

Use `set a := AdelicGLn.det K 𝒩' ((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype u)`. Establish `ha : a * a = 1`. Use `ext`. Simplify `det_trHom_mul_self b 𝔸[K] H hH u` using `[a]`. Establish `h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) * (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1`.

Establish `h3` using `congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha`. Rewrite `h3` using `[map_mul, map_one]`. Simplify using `using congrArg Subtype.val h3`. Establish `hpos` using `(GroundTheory.Global.IdeleGroup.ideleModule K a).2`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hGL : G ≤ adelicCentralizer (resScalar (ι` using `ι) b) := by`. Introduce and unpack `_ ⟨u, rfl⟩ j`. Establish `e` using `resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j`. Express the relevant statement in the definitionally equal form `_ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) = (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _`. Rewrite using `[e]`.

Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype]`. Rewrite using `[trHom_val]`. Conclude with `resHom_commute_scalar b 𝔸[K] _ _`. Take `⟨C, hC, hred⟩` from `exists_isCompact_centralizer_reduction (resScalar (ι := ι) b) G hG1 hGL hε (by rintro _ ⟨u, rfl⟩ x hx; exact hh u x hx)`. Use `⟨C, hC, fun u => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hγC⟩` from `hred _ ⟨u, rfl⟩`. Take `⟨M, hM⟩` from `exists_resHom_eq_of_commute b γ hγ`. Use `⟨inside₂ (K ⊗[K] E) M, ?_⟩` and prove the remaining obligations. Establish `e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) = AdelicGLn.diagonal K 𝒩' γ`. Use extensionality with `: 1`.

Rewrite using `[← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]`. Both sides reduce to the same expression. Rewrite using `[map_mul, map_inv, e]`. Conclude with `hγC`.
-/
theorem exists_isCompact_trHom (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ C : Set (GL (Fin 𝒩') 𝔸[K]), IsCompact C ∧ ∀ u : unitaryPoints K E H 𝔸[K],
      ∃ M : GL ι (K ⊗[K] E), trHom b 𝔸[K]
        ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) ∈ C := by
  classical
  obtain ⟨ε, hε, hh⟩ := exists_pos_le_height_trHom H b haniso
  let G : Subgroup (AdelicGLn.AdelicGL K 𝒩') :=
    ((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype).range
  have hG1 : G ≤ Reduction.normOneGL K 𝒩' := by
    rintro _ ⟨u, rfl⟩
    rw [Reduction.mem_normOneGL]
    set a := AdelicGLn.det K 𝒩' ((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype u)
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
  have hGL : G ≤ adelicCentralizer (resScalar (ι := ι) b) := by
    rintro _ ⟨u, rfl⟩ j
    have e := resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j
    change _ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) =
      (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _
    rw [e]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [trHom_val]
    exact resHom_commute_scalar b 𝔸[K] _ _
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction (resScalar (ι := ι) b) G hG1 hGL hε
    (by rintro _ ⟨u, rfl⟩ x hx; exact hh u x hx)
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨u, rfl⟩
  obtain ⟨M, hM⟩ := exists_resHom_eq_of_commute b γ hγ
  refine ⟨inside₂ (K ⊗[K] E) M, ?_⟩
  have e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) =
      AdelicGLn.diagonal K 𝒩' γ := by
    ext : 1
    rw [← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]
    rfl
  rw [map_mul, map_inv, e]
  exact hγC

end Heights

end Anisotropic

end

end GroundTheory.Automorphic

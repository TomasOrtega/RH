import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviRatHerm

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Set `φ : ((E × (Fin d₁ → E)) × E) →ₗ[E] (Fin d → E)` to `LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H'.x) (Matrix.mulVecLin H'.ι)) (LinearMap.toSpanSingleton E _ H'.y)`. Establish `hφ : ∀ p, φ p = p.1.1 • H'.x + H'.ι *ᵥ p.1.2 + p.2 • H'.y` using `fun p => by`. Simplify using `[φ, LinearMap.coprod_apply]`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]`.

Introduce `z hz`. Take `⟨a, b, u, -, -, -, rfl⟩` from `hA.split z hz`. Conclude with `⟨((a, u), b), hφ _⟩`. Establish `hrk : Module.finrank E ((E × (Fin d₁ → E)) × E) = Module.finrank E (Fin d → E)`. Simplify using `[Module.finrank_prod, hA.rank]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj`. Use `⟨fun v => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hsurj v`. Conclude with `⟨p.1.1, p.2, p.1.2, hφ p⟩`.

Establish `: φ ((0, u), 0) = φ 0` using `by rw [hφ, map_zero]; simp [hu]`. Use `hinj this` as an intermediate fact. Simplify using `using congrArg (fun p => p.1.2) this`.
-/
theorem decomp {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (hlat : Submodule.IsLattice E W.L)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) ∧
    ∀ u : Fin d₁ → E, H'.ι *ᵥ u = 0 → u = 0 := by
  let φ : ((E × (Fin d₁ → E)) × E) →ₗ[E] (Fin d → E) :=
    LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H'.x) (Matrix.mulVecLin H'.ι))
      (LinearMap.toSpanSingleton E _ H'.y)
  have hφ : ∀ p, φ p = p.1.1 • H'.x + H'.ι *ᵥ p.1.2 + p.2 • H'.y := fun p => by
    simp [φ, LinearMap.coprod_apply]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
    exact ⟨((a, u), b), hφ _⟩
  have hrk : Module.finrank E ((E × (Fin d₁ → E)) × E) = Module.finrank E (Fin d → E) := by
    simp [Module.finrank_prod, hA.rank]; ring
  have hinj : Function.Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj
  refine ⟨fun v => ?_, fun u hu => ?_⟩
  · obtain ⟨p, rfl⟩ := hsurj v
    exact ⟨p.1.1, p.2, p.1.2, hφ p⟩
  · have : φ ((0, u), 0) = φ 0 := by rw [hφ, map_zero]; simp [hu]
    have := hinj this
    simpa using congrArg (fun p => p.1.2) this

/- English proof (translation)
Take `⟨hdec, hinj⟩` from `decomp hlat hA`. Introduce `h0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hw0` to reduce the goal to its premises. Use `set w' : Fin d₁ → E := fun j => σ (w j) with hw'`.

Use `set z : Fin d → E := H'.ι *ᵥ w' with hz`. Establish `hσz : (fun i => σ (z i)) = H'.ι.map σ *ᵥ w`. Use function extensionality and compare the values at `i`. Simplify using `[hz, hw', mulVec, dotProduct, map_sum, map_mul, hσ]`. Establish `hι : ∀ u, form σ W.J (H'.ι *ᵥ u) z = 0`.

Introduce `u`. Establish `e : form σ W.J (H'.ι *ᵥ u) z = u ⬝ᵥ (W₁.J *ᵥ w)`. Rewrite using `[form, hσz, ← hA.gram, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]`. Rewrite using `[e, hw, dotProduct_zero]`. Establish `hx : form σ W.J H'.x z = 0`.

Rewrite using `[GlobalTheory.LeviUnique.form_swap σ hσ hJ z H'.x, (hA.orth w').1, map_zero]`. Establish `hy : form σ W.J H'.y z = 0`. Rewrite using `[GlobalTheory.LeviUnique.form_swap σ hσ hJ z H'.y, (hA.orth w').2, map_zero]`. Establish `hall : ∀ v, form σ W.J v z = 0`. Introduce `v`.

Take `⟨a, b, u, rfl⟩` from `hdec v`. Rewrite using `[GlobalTheory.LeviUnique.form_add_left, GlobalTheory.LeviUnique.form_add_left, GlobalTheory.LeviUnique.form_smul_left, GlobalTheory.LeviUnique.form_smul_left, hx, hy, hι]`. Simplify using the standard rewrite rules. Establish `hJz : W.J *ᵥ (fun i => σ (z i)) = 0`. Use function extensionality and compare the values at `i`.

Use `hall (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[form, single_one_dotProduct]`. Conclude with `this`. Establish `hσz0` using `Matrix.eq_zero_of_mulVec_eq_zero hdet hJz`. Establish `hz0 : z = 0`.

Use function extensionality and compare the values at `i`. Use `congrArg σ (congrFun hσz0 i)` as an intermediate fact. Simplify `this` using `[hσ]`. Use `hinj w' hz0` as an intermediate fact. Use function extensionality and compare the values at `j`.

Use `congrArg σ (congrFun this j)` as an intermediate fact. Simplify `this` using `[hw', hσ]`.
-/
theorem det_low_ne_zero (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hJ : ∀ i j, σ (W.J j i) = W.J i j) (hdet : W.J.det ≠ 0) (hlat : Submodule.IsLattice E W.L)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : W₁.J.det ≠ 0 := by
  obtain ⟨hdec, hinj⟩ := decomp hlat hA
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hw0
  set w' : Fin d₁ → E := fun j => σ (w j) with hw'
  set z : Fin d → E := H'.ι *ᵥ w' with hz
  have hσz : (fun i => σ (z i)) = H'.ι.map σ *ᵥ w := by
    funext i
    simp [hz, hw', mulVec, dotProduct, map_sum, map_mul, hσ]
  have hι : ∀ u, form σ W.J (H'.ι *ᵥ u) z = 0 := by
    intro u
    have e : form σ W.J (H'.ι *ᵥ u) z = u ⬝ᵥ (W₁.J *ᵥ w) := by
      rw [form, hσz, ← hA.gram, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm,
        dotProduct_mulVec, dotProduct_comm]
    rw [e, hw, dotProduct_zero]
  have hx : form σ W.J H'.x z = 0 := by
    rw [GlobalTheory.LeviUnique.form_swap σ hσ hJ z H'.x, (hA.orth w').1, map_zero]
  have hy : form σ W.J H'.y z = 0 := by
    rw [GlobalTheory.LeviUnique.form_swap σ hσ hJ z H'.y, (hA.orth w').2, map_zero]
  have hall : ∀ v, form σ W.J v z = 0 := by
    intro v
    obtain ⟨a, b, u, rfl⟩ := hdec v
    rw [GlobalTheory.LeviUnique.form_add_left, GlobalTheory.LeviUnique.form_add_left, GlobalTheory.LeviUnique.form_smul_left,
      GlobalTheory.LeviUnique.form_smul_left, hx, hy, hι]
    simp
  have hJz : W.J *ᵥ (fun i => σ (z i)) = 0 := by
    funext i
    have := hall (Pi.single i 1)
    rw [form, single_one_dotProduct] at this
    exact this
  have hσz0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hJz
  have hz0 : z = 0 := by
    funext i
    have := congrArg σ (congrFun hσz0 i)
    simpa [hσ] using this
  have := hinj w' hz0
  funext j
  have := congrArg σ (congrFun this j)
  simpa [hw', hσ] using this

/- English proof (translation)
Establish `hincV : ∀ (n : ℕ) (u : Fin n → E) (c : E) (v : Fin n → E), incV F (c • u + v) = (inclR (AF F) c : AE F E) • incV F u + incV F v` using `fun n u c v => by`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `inclR (AF F) (c * u i + v i) = (inclR (AF F) c : AE F E) * inclR (AF F) (u i) + inclR (AF F) (v i)`. Rewrite using `[map_add, map_mul]`. Establish `hincι : ∀ u, incV F (H.ι *ᵥ u) = incM F H.ι *ᵥ incV F u` using `fun u => by`.

Use extensionality with `i`. Simplify using `[incV, incM, RingHom.map_mulVec]`. Both sides reduce to the same expression. Establish `key : ∀ z : Fin d → E, mat h *ᵥ incV F z = mat h' *ᵥ incV F z` using `fun z => by`. Take `⟨s, r, u, rfl⟩` from `hdec z`.

Establish `e : s • H.x + H.ι *ᵥ u + r • H.y = s • H.x + (r • H.y + H.ι *ᵥ u)` using `by abel`. Rewrite using `[e, hincV, hincV, hincι]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hl.1, hl.2.1, hl.2.2, hl'.1, hl'.2.1, hl'.2.2]`. Establish `hmat : mat h = mat h'`. Use extensionality with `i j`.

Use `congrFun (key (Pi.single j 1)) i` as an intermediate fact. Establish `hs : incV F (Pi.single j (1 : E)) = Pi.single j 1`. Use extensionality with `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using `[incV]`. Simplify using `[incV, Pi.single_apply, hk]`. Rewrite `this` using `[hs]`. Simplify `this` using `[Matrix.mulVec_single_one]`. Conclude with `Subtype.ext (Units.ext hmat)`.
-/
theorem levi_eq {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin d₁) (Fin d₁) E} {H : Plane E d d₁}
    (hdec : ∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H.x + H.ι *ᵥ u + b • H.y)
    {t : (AE F E)ˣ} {h₁ : UA σ J₁} {h h' : UA σ J} (hl : mat h *ᵥ incV F H.x = t.1 • incV F H.x ∧
      mat h *ᵥ incV F H.y = cA σ (t⁻¹).1 • incV F H.y ∧ mat h * incM F H.ι = incM F H.ι * mat h₁)
    (hl' : mat h' *ᵥ incV F H.x = t.1 • incV F H.x ∧
      mat h' *ᵥ incV F H.y = cA σ (t⁻¹).1 • incV F H.y ∧ mat h' * incM F H.ι = incM F H.ι * mat h₁) : h = h' := by
  have hincV : ∀ (n : ℕ) (u : Fin n → E) (c : E) (v : Fin n → E),
      incV F (c • u + v) = (inclR (AF F) c : AE F E) • incV F u + incV F v := fun n u c v => by
    funext i
    change inclR (AF F) (c * u i + v i) = (inclR (AF F) c : AE F E) * inclR (AF F) (u i) + inclR (AF F) (v i)
    rw [map_add, map_mul]
  have hincι : ∀ u, incV F (H.ι *ᵥ u) = incM F H.ι *ᵥ incV F u := fun u => by
    ext i; simp [incV, incM, RingHom.map_mulVec]; rfl
  have key : ∀ z : Fin d → E, mat h *ᵥ incV F z = mat h' *ᵥ incV F z := fun z => by
    obtain ⟨s, r, u, rfl⟩ := hdec z
    have e : s • H.x + H.ι *ᵥ u + r • H.y = s • H.x + (r • H.y + H.ι *ᵥ u) := by abel
    rw [e, hincV, hincV, hincι]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hl.1, hl.2.1, hl.2.2, hl'.1, hl'.2.1, hl'.2.2]
  have hmat : mat h = mat h' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      ext k; by_cases hk : k = j
      · subst hk; simp [incV]
      · simp [incV, Pi.single_apply, hk]
    rw [hs] at this
    simpa [Matrix.mulVec_single_one] using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviRatHerm

namespace GlobalTheory.LeviRatHerm

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviRat

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm γ hγ`. Take `rfl` from `hH.rank`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `hdetX : (reS X Y).J.det ≠ 0`.

Introduce `h0`. Apply `GlobalTheory.LeviUnique.det_ne_zero_of_hasSig (hXY.sig w)` to reduce the goal to its premises. Rewrite using `[show (reS X Y).J.map (B.emb w).1 = ((B.emb w).1).mapMatrix (reS X Y).J from rfl, ← RingHom.map_det, h0, map_zero]`. Take `⟨hdec, -⟩` from `decomp hXY.lat hH`. Establish `hdet : X₁.J.det ≠ 0` using `det_low_ne_zero hσ hXY.herm hdetX hXY.lat hH`.

Use `set P := fromCols H.ι (cols2 H.x H.y) with hP`. Establish `hK : Pᵀ * (reS X Y).J * P.map σ = fromBlocks X₁.J 0 0 swap2` using `gram_block σ hσ B hXY.herm hH`. Use `set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef`. Establish `hKdet : IsUnit Kᵀ.det`. Rewrite using `[det_transpose, hKdef, det_fromBlocks_zero₂₁]`.

Simplify using `[swap2, det_fin_two, hdet]`. Use `set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * (reS X Y).Jᵀ) with hQ`. Establish `hQP : Q * P = 1`. Establish `: (P.map σ)ᵀ * (reS X Y).Jᵀ * P = Kᵀ`. Rewrite using `[← hK]`.

Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Take `⟨g, hg⟩` from `Subgroup.mem_subgroupOf.1 hγ`. Establish `hγm : mat γ = (g : Matrix (Fin n₁) (Fin n₁) E).map f`.

Simplify using `only [mat]`. Rewrite using `[← hg]`. Both sides reduce to the same expression. Establish `hγu : (mat γ)ᵀ * incM F X₁.J * (mat γ).map (cA σ).toRingHom = incM F X₁.J` using `γ.2`. Rewrite `hγu` using `[hγm]`.

Establish `hgu : (g : Matrix (Fin n₁) (Fin n₁) E)ᵀ * X₁.J * (g : Matrix (Fin n₁) (Fin n₁) E).map σ.toRingHom = X₁.J` using `unitary_of_map σ _ _ hγu`. Take `⟨m₀, hu, hx, hy, hι⟩` from `levi_mat σ.toRingHom hσ H.ι H.x H.y (reS X Y).J X₁.J Q hQP hK 1 g hgu`. Set `h : UA σ X.J` to `⟨Matrix.GeneralLinearGroup.map f m₀, unitary_map σ _ _ hu⟩`. Establish `hmv : ∀ v : Fin (n₁ + 2) → E, mat h *ᵥ incV F v = incV F ((m₀ : Matrix _ _ E) *ᵥ v)` using `fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm`. Establish `hl : IsLevi (W₁` using `X₁) H 1 γ h := by`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmv, hx]`. Simplify using the standard rewrite rules. Rewrite using `[hmv, hy]`. Simplify using the standard rewrite rules.

Rewrite using `[hγm] show (m₀ : Matrix _ _ E).map f * H.ι.map f = H.ι.map f * (g : Matrix (Fin n₁) (Fin n₁) E).map f`. Rewrite using `[← Matrix.map_mul, ← hι]`. Apply the tactic sequence `first | exact Matrix.map_mul.symm | exact (RingHom.map_matrix_mul' f _ _).symm | simp [Matrix.map_mul]`. Establish `heq : m 1 γ = h` using `levi_eq hdec (hm 1 γ) hl`. Rewrite using `[heq]`.

Conclude with `Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩`.
-/
theorem levi_one_mem_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ γ ∈ ratU σ X₁.J, m 1 γ ∈ ratU σ X.J := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH m hm γ hγ
  obtain rfl := hH.rank
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdetX : (reS X Y).J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.LeviUnique.det_ne_zero_of_hasSig (hXY.sig w)
    rw [show (reS X Y).J.map (B.emb w).1 = ((B.emb w).1).mapMatrix (reS X Y).J from rfl, ← RingHom.map_det, h0, map_zero]
  obtain ⟨hdec, -⟩ := decomp hXY.lat hH
  have hdet : X₁.J.det ≠ 0 := det_low_ne_zero hσ hXY.herm hdetX hXY.lat hH
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * (reS X Y).J * P.map σ = fromBlocks X₁.J 0 0 swap2 := gram_block σ hσ B hXY.herm hH
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * (reS X Y).Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * (reS X Y).Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hγ
  have hγm : mat γ = (g : Matrix (Fin n₁) (Fin n₁) E).map f := by
    simp only [mat]; rw [← hg]; rfl
  have hγu : (mat γ)ᵀ * incM F X₁.J * (mat γ).map (cA σ).toRingHom = incM F X₁.J := γ.2
  rw [hγm] at hγu
  have hgu : (g : Matrix (Fin n₁) (Fin n₁) E)ᵀ * X₁.J * (g : Matrix (Fin n₁) (Fin n₁) E).map σ.toRingHom = X₁.J :=
    unitary_of_map σ _ _ hγu
  obtain ⟨m₀, hu, hx, hy, hι⟩ := levi_mat σ.toRingHom hσ H.ι H.x H.y (reS X Y).J X₁.J Q hQP hK 1 g hgu
  let h : UA σ X.J := ⟨Matrix.GeneralLinearGroup.map f m₀, unitary_map σ _ _ hu⟩
  have hmv : ∀ v : Fin (n₁ + 2) → E, mat h *ᵥ incV F v = incV F ((m₀ : Matrix _ _ E) *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm
  have hl : IsLevi (W₁ := X₁) H 1 γ h := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmv, hx]; simp
    · rw [hmv, hy]; simp
    · rw [hγm]
      show (m₀ : Matrix _ _ E).map f * H.ι.map f = H.ι.map f * (g : Matrix (Fin n₁) (Fin n₁) E).map f
      rw [← Matrix.map_mul, ← hι]
      first | exact Matrix.map_mul.symm | exact (RingHom.map_matrix_mul' f _ _).symm | simp [Matrix.map_mul]
  have heq : m 1 γ = h := levi_eq hdec (hm 1 γ) hl
  rw [heq]
  exact Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩

end GlobalTheory.LeviRatHerm

end

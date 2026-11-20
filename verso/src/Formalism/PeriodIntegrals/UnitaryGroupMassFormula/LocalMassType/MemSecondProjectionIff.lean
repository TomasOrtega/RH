import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WProof
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LatBasis

noncomputable section

namespace PI.LocMassTypL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
  PI.LocMassTypW
open scoped TensorProduct

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n : ℕ}

def c1 (y : Fin n → Fv F v ⊗[F] E) : Fin n → Fv F v := fun i => D.π₁ (y i)

def c2 (y : Fin n → Fv F v ⊗[F] E) : Fin n → Fv F v := fun i => D.π₂ (y i)

def mkV (a b : Fin n → Fv F v) : Fin n → Fv F v ⊗[F] E := fun i => mkS v D.e (a i) (b i)

def Mj (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (Fv F v) :=
  Matrix.of fun i j => D.π₂ (inclR (F := F) (Fv F v) (J i j))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `fst_proj_split_element D.he1 D.hsc (a i) (b i)`.
-/
theorem fst_coordinate_mk (a b : Fin n → Fv F v) : c1 D (mkV D a b) = a := by
  funext i
  exact fst_proj_split_element D.he1 D.hsc (a i) (b i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `snd_proj_split_element D.he2 D.hsc (a i) (b i)`.
-/
theorem snd_coordinate_mk (a b : Fin n → Fv F v) : c2 D (mkV D a b) = b := by
  funext i
  exact snd_proj_split_element D.he2 D.hsc (a i) (b i)

include D in
/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[D.hO]`. Rewrite using `[map_mul, map_mul]`. Conclude with `⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩`.
-/
theorem oevD_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  rw [D.hO] at hx hy ⊢
  rw [map_mul, map_mul]
  exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩

/- English proof (translation)
Rewrite using `[D.hO, D.he1, D.he2]`. Conclude with `⟨one_mem _, zero_mem _⟩`.
-/
theorem e_oev : D.e ∈ OEv (E := E) v := by
  rw [D.hO, D.he1, D.he2]
  exact ⟨one_mem _, zero_mem _⟩

/- English proof (translation)
Rewrite using `[D.hO, map_sub, map_sub, map_one, map_one, D.he1, D.he2, sub_self, sub_zero]`. Conclude with `⟨zero_mem _, one_mem _⟩`.
-/
theorem e'_oev : 1 - D.e ∈ OEv (E := E) v := by
  rw [D.hO, map_sub, map_sub, map_one, map_one, D.he1, D.he2, sub_self, sub_zero]
  exact ⟨zero_mem _, one_mem _⟩

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_smulL (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • w) = c * hR (Fv F v) σ J x w := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

include D in
/- English proof (translation)
Use `(hSD (c • w)).2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hR_smulL]`. Conclude with `oevD_mul D hc ((hSD w).1 hw x hx)`.
-/
theorem latD_smul {J : Matrix (Fin n) (Fin n) E} {Λ : Set (Fin n → E)} (hSD : IsSDLoc σ J v Λ)
    {c : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v) {w : Fin n → Fv F v ⊗[F] E}
    (hw : w ∈ latLoc (E := E) v Λ) : c • w ∈ latLoc (E := E) v Λ := by
  refine (hSD (c • w)).2 fun x hx => ?_
  rw [hR_smulL]
  exact oevD_mul D hc ((hSD w).1 hw x hx)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [sigR, inclR]`.
-/
theorem sigR_inclR (a : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) a) = inclR (F := F) (Fv F v) (σ a) := by
  first
    | rfl
    | simp [sigR, inclR]

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, map_sum, map_mul, D.hσ2, JR, Matrix.map_apply, dotProduct, Matrix.mulVec, c1, c2, Mj, Matrix.of_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitian_snd_projection (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → Fv F v ⊗[F] E) :
    D.π₂ (hR (Fv F v) σ J x y) = c1 D x ⬝ᵥ (Mj D J *ᵥ c2 D y) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, D.hσ2, JR, Matrix.map_apply, dotProduct,
    Matrix.mulVec, c1, c2, Mj, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `key : ∀ i j, D.π₁ (inclR (F` using `F) (Fv F v) (J i j)) = Mj D J j i := by`. Introduce `i j`. Rewrite using `[← hJ i j, ← sigR_inclR, D.hσ1]`. Both sides reduce to the same expression. Simplify using `only [hR, Formalism.UG.hform, map_sum, map_mul, D.hσ1, JR, Matrix.map_apply, key, dotProduct, Matrix.mulVec, c1, c2, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitian_fst_projection {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → Fv F v ⊗[F] E) :
    D.π₁ (hR (Fv F v) σ J x y) = c1 D y ⬝ᵥ (Mj D J *ᵥ c2 D x) := by
  have key : ∀ i j, D.π₁ (inclR (F := F) (Fv F v) (J i j)) = Mj D J j i := by
    intro i j
    rw [← hJ i j, ← sigR_inclR, D.hσ1]
    rfl
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, D.hσ1, JR, Matrix.map_apply, key, dotProduct,
    Matrix.mulVec, c1, c2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Express the relevant statement in the definitionally equal form `D.π₁ (sc (E := E) v (c : Fv F v)) * D.π₁ x = _`. Rewrite using `[(D.hsc _).1]`.
-/
theorem fst_integer_smul (c : v.adicCompletionIntegers F) (x : Fv F v ⊗[F] E) :
    D.π₁ (c • x) = (c : Fv F v) * D.π₁ x := by
  rw [Algebra.smul_def, map_mul]
  change D.π₁ (sc (E := E) v (c : Fv F v)) * D.π₁ x = _
  rw [(D.hsc _).1]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Express the relevant statement in the definitionally equal form `D.π₂ (sc (E := E) v (c : Fv F v)) * D.π₂ x = _`. Rewrite using `[(D.hsc _).2]`.
-/
theorem snd_integer_smul (c : v.adicCompletionIntegers F) (x : Fv F v ⊗[F] E) :
    D.π₂ (c • x) = (c : Fv F v) * D.π₂ x := by
  rw [Algebra.smul_def, map_mul]
  change D.π₂ (sc (E := E) v (c : Fv F v)) * D.π₂ x = _
  rw [(D.hsc _).2]

def pr1 : (Fin n → Fv F v ⊗[F] E) →ₗ[v.adicCompletionIntegers F] (Fin n → Fv F v) where
  toFun := c1 D
  map_add' x y := by funext i; simp [c1, map_add]
  map_smul' c x := by
    funext i
    simp only [c1, Pi.smul_apply, RingHom.id_apply]
    rw [fst_integer_smul]; rfl

def pr2 : (Fin n → Fv F v ⊗[F] E) →ₗ[v.adicCompletionIntegers F] (Fin n → Fv F v) where
  toFun := c2 D
  map_add' x y := by funext i; simp [c2, map_add]
  map_smul' c x := by
    funext i
    simp only [c2, Pi.smul_apply, RingHom.id_apply]
    rw [snd_integer_smul]; rfl

/- English proof (translation)
Use `D.extV (fun i => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [mkV, c1, c2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, D.he1]`. Rewrite using `[fst_proj_split_element D.he1 D.hsc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mkV, c1, c2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, D.he2]`.

Rewrite using `[snd_proj_split_element D.he2 D.hsc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mkV_split (y z : Fin n → Fv F v ⊗[F] E) :
    mkV D (c1 D y) (c2 D z) = D.e • y + (1 - D.e) • z := by
  refine D.extV (fun i => ?_) (fun i => ?_)
  · simp only [mkV, c1, c2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
      map_one, D.he1]
    rw [fst_proj_split_element D.he1 D.hsc]
    ring
  · simp only [mkV, c1, c2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
      map_one, D.he2]
    rw [snd_proj_split_element D.he2 D.hsc]
    ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨Submodule.mem_map.2 ⟨y, hy, rfl⟩, Submodule.mem_map.2 ⟨y, hy, rfl⟩⟩`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨a, ha, hay⟩` from `Submodule.mem_map.1 h1`.

Take `⟨b, hb, hby⟩` from `Submodule.mem_map.1 h2`. Establish `hy : y = D.e • a + (1 - D.e) • b`. Establish `ha' : c1 D a = c1 D y` using `hay`. Establish `hb' : c2 D b = c2 D y` using `hby`. Rewrite using `[← mkV_split, ha', hb', mkV_split, ← add_smul]`.

Simplify using the standard rewrite rules. Rewrite using `[hy]`. Conclude with `add_mem (latD_smul D hSD (e_oev D) ha) (latD_smul D hSD (e'_oev D) hb)`.
-/
theorem mem_lat_iff {J : Matrix (Fin n) (Fin n) E} {Λ : Set (Fin n → E)} (hSD : IsSDLoc σ J v Λ)
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc (E := E) v Λ ↔ c1 D y ∈ (latLoc (E := E) v Λ).map (pr1 D) ∧
      c2 D y ∈ (latLoc (E := E) v Λ).map (pr2 D) := by
  constructor
  · intro hy
    exact ⟨Submodule.mem_map.2 ⟨y, hy, rfl⟩, Submodule.mem_map.2 ⟨y, hy, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha, hay⟩ := Submodule.mem_map.1 h1
    obtain ⟨b, hb, hby⟩ := Submodule.mem_map.1 h2
    have hy : y = D.e • a + (1 - D.e) • b := by
      have ha' : c1 D a = c1 D y := hay
      have hb' : c2 D b = c2 D y := hby
      rw [← mkV_split, ha', hb', mkV_split, ← add_smul]
      simp
    rw [hy]
    exact add_mem (latD_smul D hSD (e_oev D) ha) (latD_smul D hSD (e'_oev D) hb)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hb a ha`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hb`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 ha`. Establish `h` using `((D.hO _).1 ((hSD y).1 hy x hx)).2`.

Rewrite `h` using `[hermitian_snd_projection]`. Conclude with `h`. Introduce `h`. Use `Submodule.mem_map.2 ⟨mkV D 0 b, ?_, snd_coordinate_mk D 0 b⟩` and prove the remaining obligations. Use `(hSD _).2 fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[D.hO, hermitian_snd_projection, hermitian_fst_projection D hJ, fst_coordinate_mk, snd_coordinate_mk]`. Use `⟨?_, h _ (Submodule.mem_map.2 ⟨x, hx, rfl⟩)⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem mem_second_projection_iff {J : Matrix (Fin n) (Fin n) E} {Λ : Set (Fin n → E)} (hSD : IsSDLoc σ J v Λ)
    (hJ : ∀ i j, σ (J j i) = J i j) (b : Fin n → Fv F v) :
    b ∈ (latLoc (E := E) v Λ).map (pr2 D) ↔
      ∀ a ∈ (latLoc (E := E) v Λ).map (pr1 D), a ⬝ᵥ (Mj D J *ᵥ b) ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hb a ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 ha
    have h := ((D.hO _).1 ((hSD y).1 hy x hx)).2
    rw [hermitian_snd_projection] at h
    exact h
  · intro h
    refine Submodule.mem_map.2 ⟨mkV D 0 b, ?_, snd_coordinate_mk D 0 b⟩
    refine (hSD _).2 fun x hx => ?_
    rw [D.hO, hermitian_snd_projection, hermitian_fst_projection D hJ, fst_coordinate_mk, snd_coordinate_mk]
    refine ⟨?_, h _ (Submodule.mem_map.2 ⟨x, hx, rfl⟩)⟩
    simp

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `a _`. Set `T : Submodule (Fv F v) (Fin n → Fv F v)` to `Submodule.span (Fv F v) (((latLoc (E := E) v Λ).map (pr1 D) : Submodule _ _) : Set (Fin n → Fv F v))`. Set `S : Submodule (Fv F v ⊗[F] E) (Fin n → Fv F v ⊗[F] E)` to `{ carrier := {y | c1 D y ∈ T} add_mem' := fun {x y} hx hy => by`. Establish `h1 : c1 D (x + y) = c1 D x + c1 D y`.

Use function extensionality and compare the values at `i`. Simplify using `[c1, map_add]`. Use `show c1 D (x + y) ∈ T`. Rewrite using `[h1]`. Conclude with `add_mem hx hy`.

Use the proof step `zero_mem' := by`. Establish `h0 : c1 D (0 : Fin n → Fv F v ⊗[F] E) = 0`. Use function extensionality and compare the values at `i`. Simplify using `[c1]`. Use `show c1 D 0 ∈ T`.

Rewrite using `[h0]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun r y hy => by`. Establish `h2 : c1 D (r • y) = D.π₁ r • c1 D y`. Use function extensionality and compare the values at `i`.

Simplify using `[c1, map_mul, smul_eq_mul]`. Use `show c1 D (r • y) ∈ T`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ hy }`. Establish `hle : Submodule.span (Fv F v ⊗[F] E) (latLoc (E` using `E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) ≤ S := by`.

Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Conclude with `Submodule.subset_span (Submodule.mem_map.2 ⟨y, hy, rfl⟩)`. Rewrite `hle` using `[hsp]`. Establish `h : mkV D a 0 ∈ S` using `hle Submodule.mem_top`.

Establish `h' : c1 D (mkV D a 0) ∈ T` using `h`. Rewrite `h'` using `[fst_coordinate_mk]`. Then use the resulting hypothesis.
-/
theorem span_first_projection {Λ : Set (Fin n → E)}
    (hsp : Submodule.span (Fv F v ⊗[F] E) (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) = ⊤) :
    Submodule.span (Fv F v) (((latLoc (E := E) v Λ).map (pr1 D) : Submodule _ _) :
      Set (Fin n → Fv F v)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  let T : Submodule (Fv F v) (Fin n → Fv F v) := Submodule.span (Fv F v)
    (((latLoc (E := E) v Λ).map (pr1 D) : Submodule _ _) : Set (Fin n → Fv F v))
  let S : Submodule (Fv F v ⊗[F] E) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := {y | c1 D y ∈ T}
      add_mem' := fun {x y} hx hy => by
        have h1 : c1 D (x + y) = c1 D x + c1 D y := by
          funext i
          simp [c1, map_add]
        show c1 D (x + y) ∈ T
        rw [h1]
        exact add_mem hx hy
      zero_mem' := by
        have h0 : c1 D (0 : Fin n → Fv F v ⊗[F] E) = 0 := by
          funext i
          simp [c1]
        show c1 D 0 ∈ T
        rw [h0]
        exact zero_mem _
      smul_mem' := fun r y hy => by
        have h2 : c1 D (r • y) = D.π₁ r • c1 D y := by
          funext i
          simp [c1, map_mul, smul_eq_mul]
        show c1 D (r • y) ∈ T
        rw [h2]
        exact Submodule.smul_mem _ _ hy }
  have hle : Submodule.span (Fv F v ⊗[F] E)
      (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) ≤ S := by
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.subset_span (Submodule.mem_map.2 ⟨y, hy, rfl⟩)
  rw [hsp] at hle
  have h : mkV D a 0 ∈ S := hle Submodule.mem_top
  have h' : c1 D (mkV D a 0) ∈ T := h
  rwa [fst_coordinate_mk] at h'

/- English proof (translation)
Establish `h : Mj D J = (D.π₂.comp (inclR (F` using `F) (Fv F v))).mapMatrix J := by`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h, ← RingHom.map_det]`. Conclude with `(isUnit_iff_ne_zero.2 hdet).map _`.
-/
theorem isUnit_Mj {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) : IsUnit (Mj D J).det := by
  have h : Mj D J = (D.π₂.comp (inclR (F := F) (Fv F v))).mapMatrix J := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det]
  exact (isUnit_iff_ne_zero.2 hdet).map _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h j`. Establish `hc : ∀ i, (Pi.single j (1 : Fv F v) : Fin n → Fv F v) i ∈ v.adicCompletionIntegers F`. Introduce `i`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `h1` using `h (Pi.single j 1) hc`. Simplify using `using h1`.

Introduce `h c hc`. Simplify using `only [dotProduct]`. Conclude with `sum_mem fun i _ => mul_mem (hc i) (h i)`.
-/
theorem dot_int_iff (w : Fin n → Fv F v) :
    (∀ c : Fin n → Fv F v, (∀ i, c i ∈ v.adicCompletionIntegers F) → c ⬝ᵥ w ∈ v.adicCompletionIntegers F) ↔
      ∀ j, w j ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h j
    have hc : ∀ i, (Pi.single j (1 : Fv F v) : Fin n → Fv F v) i ∈ v.adicCompletionIntegers F := by
      intro i
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h1 := h (Pi.single j 1) hc
    simpa using h1
  · intro h c hc
    simp only [dotProduct]
    exact sum_mem fun i _ => mul_mem (hc i) (h i)

include D in

/- English proof (translation)
Take `⟨A, hAu, hA⟩` from `lat_basis v ((latLoc (E := E) v Λ).map (pr1 D)) (hLat.1.map _) (span_first_projection D hLat.2)`. Establish `hAd : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det A).1 hAu`. Establish `hMd` using `isUnit_Mj D hJ.2`. Use `set N := Aᵀ * Mj D J with hNdef`. Establish `hNd : IsUnit N.det`.

Rewrite using `[hNdef, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `hAd.mul hMd`. Use `set B := N⁻¹ with hBdef`. Establish `hL2 : ∀ b, b ∈ (latLoc (E` using `E) v Λ).map (pr2 D) ↔ ∃ d : Fin n → Fv F v, (∀ i, d i ∈ v.adicCompletionIntegers F) ∧ b = B *ᵥ d := by`. Introduce `b`.

Rewrite using `[mem_second_projection_iff D hSD hJ.1]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨N *ᵥ b, (dot_int_iff (N *ᵥ b)).1 fun c hc => ?_, ?_⟩` and prove the remaining obligations. Use `h (A *ᵥ c) ((hA _).2 ⟨c, hc, rfl⟩)` as an intermediate fact.

Rewrite using `[show A *ᵥ c ⬝ᵥ (Mj D J *ᵥ b) = c ⬝ᵥ (N *ᵥ b) by` and apply the resulting hypothesis. Rewrite `this` using `[dot_mulVec_mulVec, hNdef]]`. Rewrite using `[hBdef, mulVec_mulVec, nonsing_inv_mul _ hNd, one_mulVec]`. Introduce and unpack `⟨d, hd, rfl⟩ a ha`. Take `⟨c, hc, rfl⟩` from `(hA a).1 ha`.

Rewrite using `[show A *ᵥ c ⬝ᵥ (Mj D J *ᵥ (B *ᵥ d)) = c ⬝ᵥ d by`. Rewrite using `[mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc, ← hNdef, hBdef, mul_nonsing_inv _ hNd, one_mulVec]]`. Conclude with `(dot_int_iff d).2 hd c hc`. Set `Q : GL (Fin n) (Fv F v ⊗[F] E)` to `⟨D.kS A B, D.kS A⁻¹ N, by rw [D.kS_mul, mul_nonsing_inv _ hAd, hBdef, nonsing_inv_mul _ hNd, D.kS_one], by rw [D.kS_mul, nonsing_inv_mul _ hAd, hBdef, mul_nonsing_inv _ hNd, D.kS_one]⟩`. Establish `hQ1 : ∀ x, c1 D ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) = A *ᵥ c1 D x` using `fun x => by`.

Use function extensionality and compare the values at `i`. Conclude with `D.fst_proj_split_matrix_mulVec A B x i`. Establish `hQ2 : ∀ x, c2 D ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) = B *ᵥ c2 D x` using `fun x => by`. Use function extensionality and compare the values at `i`. Conclude with `D.snd_proj_split_matrix_mulVec A B x i`.

Use `⟨Q, fun y => ?_, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_lat_iff D hSD, hA, hL2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨c, hc, h1⟩, ⟨d, hd, h2⟩⟩`. Use `⟨mkV D c d, fun i => (D.hO _).2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[show D.π₁ (mkV D c d i) = c i from congrFun (fst_coordinate_mk D c d) i]`. Conclude with `hc i`. Rewrite using `[show D.π₂ (mkV D c d i) = d i from congrFun (snd_coordinate_mk D c d) i]`. Conclude with `hd i`. Apply `D.extV` to reduce the goal to its premises.

Introduce `i`. Use `congrFun (hQ1 (mkV D c d)) i` as an intermediate fact. Rewrite `this` using `[fst_coordinate_mk]`. Conclude with `(congrFun h1 i).trans this.symm`. Introduce `i`.

Use `congrFun (hQ2 (mkV D c d)) i` as an intermediate fact. Rewrite `this` using `[snd_coordinate_mk]`. Conclude with `(congrFun h2 i).trans this.symm`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨c1 D x, fun i => ((D.hO _).1 (hx i)).1, hQ1 x⟩, ⟨c2 D x, fun i => ((D.hO _).1 (hx i)).2, hQ2 x⟩⟩`.

Use `show _ = stdH σ x y`. Apply `D.ext` to reduce the goal to its premises. Rewrite using `[hermitian_fst_projection D hJ.1, SD.fst_proj_standard_hermitian_form, hQ1, hQ2, mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc, ← hNdef, hBdef, mul_nonsing_inv _ hNd, one_mulVec, dotProduct_comm]`. Both sides reduce to the same expression. Rewrite using `[hermitian_snd_projection, SD.snd_proj_standard_hermitian_form, hQ1, hQ2, mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc, ← hNdef, hBdef, mul_nonsing_inv _ hNd, one_mulVec]`.

Both sides reduce to the same expression.
-/
theorem latStd_SD {J : Matrix (Fin n) (Fin n) E} {Λ : Set (Fin n → E)} (hJ : IsHermND σ J)
    (hSD : IsSDLoc σ J v Λ) (hLat : LocMassOrdW.IsLatLoc v Λ) :
    ∃ Q : GL (Fin n) (Fv F v ⊗[F] E),
      (∀ y, y ∈ latLoc (E := E) v Λ ↔
        ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
          y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) ∧
      ∀ x y : Fin n → Fv F v ⊗[F] E,
        hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i := by
  classical
  obtain ⟨A, hAu, hA⟩ := lat_basis v ((latLoc (E := E) v Λ).map (pr1 D)) (hLat.1.map _)
    (span_first_projection D hLat.2)
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hAu
  have hMd := isUnit_Mj D hJ.2
  set N := Aᵀ * Mj D J with hNdef
  have hNd : IsUnit N.det := by
    rw [hNdef, Matrix.det_mul, Matrix.det_transpose]; exact hAd.mul hMd
  set B := N⁻¹ with hBdef
  have hL2 : ∀ b, b ∈ (latLoc (E := E) v Λ).map (pr2 D) ↔
      ∃ d : Fin n → Fv F v, (∀ i, d i ∈ v.adicCompletionIntegers F) ∧ b = B *ᵥ d := by
    intro b
    rw [mem_second_projection_iff D hSD hJ.1]
    constructor
    · intro h
      refine ⟨N *ᵥ b, (dot_int_iff (N *ᵥ b)).1 fun c hc => ?_, ?_⟩
      · have := h (A *ᵥ c) ((hA _).2 ⟨c, hc, rfl⟩)
        rwa [show A *ᵥ c ⬝ᵥ (Mj D J *ᵥ b) = c ⬝ᵥ (N *ᵥ b) by
          rw [dot_mulVec_mulVec, hNdef]] at this
      · rw [hBdef, mulVec_mulVec, nonsing_inv_mul _ hNd, one_mulVec]
    · rintro ⟨d, hd, rfl⟩ a ha
      obtain ⟨c, hc, rfl⟩ := (hA a).1 ha
      rw [show A *ᵥ c ⬝ᵥ (Mj D J *ᵥ (B *ᵥ d)) = c ⬝ᵥ d by
        rw [mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc, ← hNdef, hBdef,
          mul_nonsing_inv _ hNd, one_mulVec]]
      exact (dot_int_iff d).2 hd c hc
  let Q : GL (Fin n) (Fv F v ⊗[F] E) :=
    ⟨D.kS A B, D.kS A⁻¹ N, by rw [D.kS_mul, mul_nonsing_inv _ hAd, hBdef, nonsing_inv_mul _ hNd, D.kS_one],
      by rw [D.kS_mul, nonsing_inv_mul _ hAd, hBdef, mul_nonsing_inv _ hNd, D.kS_one]⟩
  have hQ1 : ∀ x, c1 D ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) = A *ᵥ c1 D x := fun x => by
    funext i; exact D.fst_proj_split_matrix_mulVec A B x i
  have hQ2 : ∀ x, c2 D ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) = B *ᵥ c2 D x := fun x => by
    funext i; exact D.snd_proj_split_matrix_mulVec A B x i
  refine ⟨Q, fun y => ?_, fun x y => ?_⟩
  · rw [mem_lat_iff D hSD, hA, hL2]
    constructor
    · rintro ⟨⟨c, hc, h1⟩, ⟨d, hd, h2⟩⟩
      refine ⟨mkV D c d, fun i => (D.hO _).2 ⟨?_, ?_⟩, ?_⟩
      · rw [show D.π₁ (mkV D c d i) = c i from congrFun (fst_coordinate_mk D c d) i]; exact hc i
      · rw [show D.π₂ (mkV D c d i) = d i from congrFun (snd_coordinate_mk D c d) i]; exact hd i
      · apply D.extV
        · intro i
          have := congrFun (hQ1 (mkV D c d)) i
          rw [fst_coordinate_mk] at this
          exact (congrFun h1 i).trans this.symm
        · intro i
          have := congrFun (hQ2 (mkV D c d)) i
          rw [snd_coordinate_mk] at this
          exact (congrFun h2 i).trans this.symm
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨c1 D x, fun i => ((D.hO _).1 (hx i)).1, hQ1 x⟩,
        ⟨c2 D x, fun i => ((D.hO _).1 (hx i)).2, hQ2 x⟩⟩
  · show _ = stdH σ x y
    apply D.ext
    · rw [hermitian_fst_projection D hJ.1, SD.fst_proj_standard_hermitian_form, hQ1, hQ2, mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc,
        ← hNdef, hBdef, mul_nonsing_inv _ hNd, one_mulVec, dotProduct_comm]
      rfl
    · rw [hermitian_snd_projection, SD.snd_proj_standard_hermitian_form, hQ1, hQ2, mulVec_mulVec, dot_mulVec_mulVec, ← Matrix.mul_assoc,
        ← hNdef, hBdef, mul_nonsing_inv _ hNd, one_mulVec]
      rfl

end Std

/- English proof (translation)
Take `⟨e, π₁, π₂, -, -, h1, h2, he1, he2, hsc, hσ2, hσ1, hO⟩` from `hS σ J ψ v hStd hUn hEta`. Conclude with `⟨⟨e, π₁, π₂, h1, h2, he1, he2, hsc, hσ1, hσ2, hO⟩⟩`.
-/
theorem exists_SD (hS : SplitR) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hStd : StdHyp σ J ψ) (hUn : UnramAt (E := E) v)
    (hEta : etaV (E := E) v = 1) : Nonempty (SD σ v) := by
  obtain ⟨e, π₁, π₂, -, -, h1, h2, he1, he2, hsc, hσ2, hσ1, hO⟩ := hS σ J ψ v hStd hUn hEta
  exact ⟨⟨e, π₁, π₂, h1, h2, he1, he2, hsc, hσ1, hσ2, hO⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v Λ hStd hSD hUn hEta hLat`. Take `⟨D⟩` from `exists_SD hS σ J ψ v hStd hUn hEta`. Conclude with `latStd_SD D hStd.2.1 hSD hLat`.
-/
theorem latStd_of (hS : SplitR) : LatStd := by
  intro F E _ _ _ _ _ σ n J ψ v Λ hStd hSD hUn hEta hLat
  obtain ⟨D⟩ := exists_SD hS σ J ψ v hStd hUn hEta
  exact latStd_SD D hStd.2.1 hSD hLat

end PI.LocMassTypL

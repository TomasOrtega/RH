import Formalism.LocalToGlobal.Columns.RecLevelCls

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section Pad

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Simplify using `[padM]`.
-/
theorem til_tmv_padM_cc (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : padM R n A i.castSucc j.castSucc = A i j := by
  simp [padM]

/- English proof (translation)
Simplify using `[padM]`.
-/
theorem til_tmv_padM_cl (A : Matrix (Fin n) (Fin n) R) (i : Fin n) : padM R n A i.castSucc (Fin.last n) = 0 := by
  simp [padM]

/- English proof (translation)
Simplify using `[padM]`.
-/
theorem til_tmv_padM_lc (A : Matrix (Fin n) (Fin n) R) (j : Fin n) : padM R n A (Fin.last n) j.castSucc = 0 := by
  simp [padM]

/- English proof (translation)
Simplify using `[padM]`.
-/
theorem til_tmv_padM_ll (A : Matrix (Fin n) (Fin n) R) : padM R n A (Fin.last n) (Fin.last n) = 1 := by
  simp [padM]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Simplify using `[cT, til_tmv_padM_cc, til_tmv_padM_cl, til_tmv_padM_lc, til_tmv_padM_ll]`.
-/
theorem til_tmv_cT_padM (σ : R →+* R) (A : Matrix (Fin n) (Fin n) R) : cT σ (padM R n A) = padM R n (cT σ A) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [cT, til_tmv_padM_cc, til_tmv_padM_cl, til_tmv_padM_lc, til_tmv_padM_ll]

/- English proof (translation)
Establish `h : cT σ (y : Matrix (Fin n) (Fin n) R) * 1 * (y : Matrix (Fin n) (Fin n) R) = 1` using `hy`. Use `show cT σ ((Units.map (padM R n) y : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * 1 * ((Units.map (padM R n) y : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1`. Rewrite `h` using `[Matrix.mul_one]`. Rewrite using `[Units.coe_map, Matrix.mul_one, til_tmv_cT_padM, ← map_mul, h, map_one]`.
-/
theorem til_tmv_padM_UJ (σ : R →+* R) {y : GL (Fin n) R} (hy : y ∈ UJ σ (1 : Matrix (Fin n) (Fin n) R)) :
    Units.map (padM R n) y ∈ UJ σ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  have h : cT σ (y : Matrix (Fin n) (Fin n) R) * 1 * (y : Matrix (Fin n) (Fin n) R) = 1 := hy
  show cT σ ((Units.map (padM R n) y : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * 1 *
      ((Units.map (padM R n) y : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1
  rw [Matrix.mul_one] at h
  rw [Units.coe_map, Matrix.mul_one, til_tmv_cT_padM, ← map_mul, h, map_one]

/- English proof (translation)
Establish `hcol : ∀ (a : Fin (n + 1)) (b : Fin n), g a b.castSucc = (ι * y) a b`. Introduce `a b`. Rewrite using `[← h1, Matrix.mul_apply, Fin.sum_univ_castSucc]`. Simplify using `[hι1, hι2]`. Establish `hrow : ∀ a : Fin (n + 1), g a (Fin.last n) * z (Fin.last n) = z a`.

Introduce `a`. Establish `e` using `congrFun h2 a`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, mul_zero, Finset.sum_const_zero, zero_add] at e`. Conclude with `e`. Take `⟨u, hu⟩` from `hz2`.

Use extensionality with `a b`. Use `Fin.lastCases ?_ (fun b' => ?_) b` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun a' => ?_) a` and prove the remaining obligations. Establish `e` using `hrow (Fin.last n)`. Rewrite using `[til_tmv_padM_ll]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hu, Units.mul_inv_cancel_right]`. Use `_ = z (Fin.last n) * ↑u⁻¹ := by rw [e]`. Use `_ = 1 := by rw [← hu, Units.mul_inv]`. Establish `e` using `hrow a'.castSucc`.

Rewrite `e` using `[hz1]`. Rewrite using `[til_tmv_padM_cl]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hu, Units.mul_inv_cancel_right]`. Use `_ = 0 := by rw [e, zero_mul]`.

Rewrite using `[hcol]`. Use `Fin.lastCases ?_ (fun a' => ?_) a` and prove the remaining obligations. Rewrite using `[til_tmv_padM_lc, Matrix.mul_apply]`. Simplify using `[hι2]`. Rewrite using `[til_tmv_padM_cc, Matrix.mul_apply]`.

Simplify using `[hι1]`.
-/
theorem til_tmv_eq_padM (ι : Matrix (Fin (n + 1)) (Fin n) R) (hι1 : ∀ a b : Fin n, ι a.castSucc b = if a = b then 1 else 0)
    (hι2 : ∀ b : Fin n, ι (Fin.last n) b = 0) (z : Fin (n + 1) → R) (hz1 : ∀ a : Fin n, z a.castSucc = 0)
    (hz2 : IsUnit (z (Fin.last n))) (y : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h1 : g * ι = ι * y) (h2 : g *ᵥ z = z) : g = padM R n y := by
  have hcol : ∀ (a : Fin (n + 1)) (b : Fin n), g a b.castSucc = (ι * y) a b := by
    intro a b
    rw [← h1, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp [hι1, hι2]
  have hrow : ∀ a : Fin (n + 1), g a (Fin.last n) * z (Fin.last n) = z a := by
    intro a
    have e := congrFun h2 a
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, mul_zero, Finset.sum_const_zero,
      zero_add] at e
    exact e
  obtain ⟨u, hu⟩ := hz2
  ext a b
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · refine Fin.lastCases ?_ (fun a' => ?_) a
    · have e := hrow (Fin.last n)
      rw [til_tmv_padM_ll]
      calc g (Fin.last n) (Fin.last n)
          = g (Fin.last n) (Fin.last n) * z (Fin.last n) * ↑u⁻¹ := by
            rw [← hu, Units.mul_inv_cancel_right]
        _ = z (Fin.last n) * ↑u⁻¹ := by rw [e]
        _ = 1 := by rw [← hu, Units.mul_inv]
    · have e := hrow a'.castSucc
      rw [hz1] at e
      rw [til_tmv_padM_cl]
      calc g a'.castSucc (Fin.last n)
          = g a'.castSucc (Fin.last n) * z (Fin.last n) * ↑u⁻¹ := by
            rw [← hu, Units.mul_inv_cancel_right]
        _ = 0 := by rw [e, zero_mul]
  · rw [hcol]
    refine Fin.lastCases ?_ (fun a' => ?_) a
    · rw [til_tmv_padM_lc, Matrix.mul_apply]
      simp [hι2]
    · rw [til_tmv_padM_cc, Matrix.mul_apply]
      simp [hι1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use extensionality with `a b`. Use `Fin.lastCases ?_ (fun a' => ?_) a` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, til_tmv_padM_lc, til_tmv_padM_ll, hι1, hι2]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, til_tmv_padM_cc, til_tmv_padM_cl, hι1, hι2]`.

Use function extensionality and compare the values at `a`. Use `Fin.lastCases ?_ (fun a' => ?_) a` and prove the remaining obligations. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, til_tmv_padM_ll]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, til_tmv_padM_cl]`.
-/
theorem til_tmv_padM_ext (ι : Matrix (Fin (n + 1)) (Fin n) R) (hι1 : ∀ a b : Fin n, ι a.castSucc b = if a = b then 1 else 0)
    (hι2 : ∀ b : Fin n, ι (Fin.last n) b = 0) (z : Fin (n + 1) → R) (hz1 : ∀ a : Fin n, z a.castSucc = 0)
    (y : Matrix (Fin n) (Fin n) R) : padM R n y * ι = ι * y ∧ padM R n y *ᵥ z = z := by
  constructor
  · ext a b
    refine Fin.lastCases ?_ (fun a' => ?_) a
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, til_tmv_padM_lc, til_tmv_padM_ll, hι1, hι2]
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, til_tmv_padM_cc, til_tmv_padM_cl, hι1, hι2]
  · funext a
    refine Fin.lastCases ?_ (fun a' => ?_) a
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, til_tmv_padM_ll]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz1, til_tmv_padM_cl]

end Pad

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def padA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) →* GL (Fin (n + 1)) (E ⊗[F] Formalism.L2.Herm.Af F) :=
  Units.map (padM (E ⊗[F] Formalism.L2.Herm.Af F) n)

/- English proof (translation)
Establish `h1 : ∀ m : ℕ, ((1 : Matrix (Fin m) (Fin m) E).map (inclE (F` using `F) (Formalism.L2.Herm.Af F))) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hy'` using `hy`. Simplify using `only [UAd, Formalism.L2.DIV.UA, UPts, h1] at hy' ⊢`. Simplify using `only [padA]`. Conclude with `til_tmv_padM_UJ _ hy'`.
-/
theorem padA_mem_UAd (hc : CMData F E) {n : ℕ} {y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hy : y ∈ UAd hc n) :
    padA F E n y ∈ UAd hc (n + 1) := by
  have h1 : ∀ m : ℕ, ((1 : Matrix (Fin m) (Fin m) E).map (inclE (F := F) (Formalism.L2.Herm.Af F))) = 1 :=
    fun m => Matrix.map_one _ (map_zero _) (map_one _)
  have hy' := hy
  simp only [UAd, Formalism.L2.DIV.UA, UPts, h1] at hy' ⊢
  simp only [padA]
  exact til_tmv_padM_UJ _ hy'

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [pullV]`. Rewrite using `[← map_inv (padA F E n) y]`. Simplify using `only [padA, Units.coe_map]`. Use `Fin.lastCases ?_ (fun i' => ?_) i` and prove the remaining obligations.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, til_tmv_padM_lc, til_tmv_padM_ll]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, til_tmv_padM_cc, til_tmv_padM_cl, initL]`.
-/
theorem til_tmv_pullV {n : ℕ} (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : Fin (n + 1) → E) :
    pullV (padA F E n y) v =
      Fin.snoc (α := fun _ => E ⊗[F] Formalism.L2.Herm.Af F) (pullV y (initL E n v)) (iA F E (v (Fin.last n))) := by
  funext i
  simp only [pullV]
  rw [← map_inv (padA F E n) y]
  simp only [padA, Units.coe_map]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, til_tmv_padM_lc, til_tmv_padM_ll]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, til_tmv_padM_cc, til_tmv_padM_cl, initL]

/- English proof (translation)
Establish `h1 : (fun _ : Fin 1 => a) ∈ Formalism.UG.CS.globLat (F` using `F) (1 : GL (Fin 1) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E 1) := by`. Rewrite using `[mem_globLat]`. Introduce `i`. Rewrite using `[pullV_one]`. Conclude with `h`.

Rewrite `h1` using `[globLat_one_std, mem_stdLat]`. Conclude with `h1 0`.
-/
theorem til_tmv_int_of_iA {a : E} (h : iA F E a ∈ Formalism.L2.Herm.intAf F E) : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := by
  have h1 : (fun _ : Fin 1 => a) ∈ Formalism.UG.CS.globLat (F := F) (1 : GL (Fin 1) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E 1) := by
    rw [mem_globLat]
    intro i
    rw [pullV_one]
    exact h
  rw [globLat_one_std, mem_stdLat] at h1
  exact h1 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu`. Set `T : Submodule (Formalism.L2.Herm.intAf F E) (Fin m → E ⊗[F] Formalism.L2.Herm.Af F)` to `{ carrier := {v | ∀ i, v i ∈ Formalism.L2.Herm.intAf F E} add_mem' := fun ha hb i => add_mem (ha i) (hb i) zero_mem' := fun _ => zero_mem _ smul_mem' := fun c v hv i => by show (c : E ⊗[F] Formalism.L2.Herm.Af F) * v i ∈ Formalism.L2.Herm.intAf F E`. Conclude with `mul_mem c.2 (hv i) }`. Establish `hle : latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E m) ≤ T := by`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `∀ i, inclE (F := F) (Formalism.L2.Herm.Af F) (x i) ∈ Formalism.L2.Herm.intAf F E`. Introduce `i`. Establish `hx' : x ∈ stdLat E m` using `hx`.

Unfold `stdLat at hx'`. Take `⟨b, hb⟩` from `Submodule.mem_one.1 (Submodule.mem_pi.1 hx' i (Set.mem_univ _))`. Rewrite using `[← hb]`. Conclude with `Formalism.UG.CS.incl_int b`. Conclude with `hle hu`.

Introduce `hu`. Establish `e : u = ∑ i, (⟨u i, hu i⟩ : Formalism.L2.Herm.intAf F E) • (Pi.single i (1 : E ⊗[F] Formalism.L2.Herm.Af F) : Fin m → E ⊗[F] Formalism.L2.Herm.Af F)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Subring.smul_def]`. Rewrite using `[e]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single i 1, ?_, ?_⟩)` and prove the remaining obligations. Use `show Pi.single i (1 : E) ∈ stdLat E m`. Unfold `stdLat`. Use `Submodule.mem_pi.2 fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
private lemma latS_std_lemma_3 (m : ℕ) (u : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    u ∈ latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E m) ↔
      ∀ i, u i ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hu
    let T : Submodule (Formalism.L2.Herm.intAf F E) (Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { carrier := {v | ∀ i, v i ∈ Formalism.L2.Herm.intAf F E}
        add_mem' := fun ha hb i => add_mem (ha i) (hb i)
        zero_mem' := fun _ => zero_mem _
        smul_mem' := fun c v hv i => by
          show (c : E ⊗[F] Formalism.L2.Herm.Af F) * v i ∈ Formalism.L2.Herm.intAf F E
          exact mul_mem c.2 (hv i) }
    have hle : latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E m) ≤ T := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      change ∀ i, inclE (F := F) (Formalism.L2.Herm.Af F) (x i) ∈ Formalism.L2.Herm.intAf F E
      intro i
      have hx' : x ∈ stdLat E m := hx
      unfold stdLat at hx'
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (Submodule.mem_pi.1 hx' i (Set.mem_univ _))
      rw [← hb]
      exact Formalism.UG.CS.incl_int b
    exact hle hu
  · intro hu
    have e : u = ∑ i, (⟨u i, hu i⟩ : Formalism.L2.Herm.intAf F E) •
        (Pi.single i (1 : E ⊗[F] Formalism.L2.Herm.Af F) : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single i 1, ?_, ?_⟩)
    · show Pi.single i (1 : E) ∈ stdLat E m
      unfold stdLat
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    · funext j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]

/- English proof (translation)
Unfold `tilN`. Rewrite using `[Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, z, hz, rfl⟩`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hy`.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Use `⟨?_, a, ?_⟩` and prove the remaining obligations. Establish `hv' : initL E n ((incl E n).restrictScalars (𝓞 E) v + a • eLast E n) = v`. Use function extensionality and compare the values at `i`. Simplify using `[initL, incl, eLast, Fin.castSucc_ne_last]`.

Rewrite using `[hv']`. Conclude with `hv`. Simplify using `[incl, eLast, Algebra.smul_def]`. Introduce and unpack `⟨hx, r, hr⟩`. Use `⟨(incl E n).restrictScalars (𝓞 E) (initL E n x), Submodule.mem_map.2 ⟨_, hx, rfl⟩, r • eLast E n, Submodule.mem_span_singleton.2 ⟨r, rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[incl, eLast, hr, Algebra.smul_def]`. Simplify using `[incl, eLast, initL, Fin.castSucc_ne_last]`.
-/
private lemma mem_tilN_lemma_4 {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (x : Sp E (n + 1)) :
    x ∈ tilN N ↔ initL E n x ∈ N ∧ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x (Fin.last n) := by
  unfold tilN
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨?_, a, ?_⟩
    · have hv' : initL E n ((incl E n).restrictScalars (𝓞 E) v + a • eLast E n) = v := by
        funext i
        simp [initL, incl, eLast, Fin.castSucc_ne_last]
      rw [hv']
      exact hv
    · simp [incl, eLast, Algebra.smul_def]
  · rintro ⟨hx, r, hr⟩
    refine ⟨(incl E n).restrictScalars (𝓞 E) (initL E n x), Submodule.mem_map.2 ⟨_, hx, rfl⟩, r • eLast E n,
      Submodule.mem_span_singleton.2 ⟨r, rfl⟩, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl, eLast, hr, Algebra.smul_def]
    · simp [incl, eLast, initL, Fin.castSucc_ne_last]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_tilN_lemma_4]`. Express the relevant statement in the definitionally equal form `pullV (padA F E n y) x ∈ latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E (n + 1)) ↔ _`. Rewrite using `[til_tmv_pullV, latS_std_lemma_3]`. Simplify using `only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]`.

Use `and_congr ?_ ?_` and prove the remaining obligations. Conclude with `(latS_std_lemma_3 n (pullV y (initL E n x))).symm`. Prove the components needed by the constructor for the conclusion. Conclude with `til_tmv_int_of_iA`. Introduce and unpack `⟨r, hr⟩`.

Rewrite using `[← hr]`. Conclude with `Formalism.UG.CS.incl_int r`.
-/
theorem til_tmv_globLat {n : ℕ} (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    Formalism.UG.CS.globLat (padA F E n y) (stdLat E (n + 1)) = tilN (Formalism.UG.CS.globLat y (stdLat E n)) := by
  ext x
  rw [mem_tilN_lemma_4]
  change pullV (padA F E n y) x ∈ latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E (n + 1)) ↔ _
  rw [til_tmv_pullV, latS_std_lemma_3]
  simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]
  refine and_congr ?_ ?_
  · exact (latS_std_lemma_3 n (pullV y (initL E n x))).symm
  · constructor
    · exact til_tmv_int_of_iA
    · rintro ⟨r, hr⟩
      rw [← hr]
      exact Formalism.UG.CS.incl_int r

/- English proof (translation)
Use `ext`. Simplify using `[lastIdx]`.
-/
theorem til_tmv_lastIdx (n : ℕ) [NeZero (n + 1)] : lastIdx (n + 1) = Fin.last n := by
  ext
  simp [lastIdx]

/- English proof (translation)
Use `haveI : P.asIdeal.IsMaximal := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Establish `hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Establish `hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r ∧ Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r` using `⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by`.

Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩`. Unfold `redP`. Rewrite using `[dif_pos hex]`. Take `⟨r', s', hs', h', hc'⟩` from `hex.choose_spec`. Establish `hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Establish `key : s * r' = s' * r`. Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← h', ← h]`. Expand and normalize the polynomial expressions, which then agree.

Apply `mul_left_cancel₀ hs'0` to reduce the goal to its premises. Rewrite using `[mul_left_comm, hc', ← map_mul, ← map_mul, key]`.
-/
private lemma mk_mul_reduction_eq_mk (P : HeightOneSpectrum (𝓞 E)) {x : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P x = Ideal.Quotient.mk P.asIdeal r := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have key : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← h', ← h]
    ring
  apply mul_left_cancel₀ hs'0
  rw [mul_left_comm, hc', ← map_mul, ← map_mul, key]

/- English proof (translation)
Establish `e : (⟨x, hx⟩ : Formalism.L2.Herm.intAf F E) = oToS F E r` using `Subtype.ext hxr`. Establish `h2 : Ideal.Quotient.mk (idS F P.asIdeal) (oToS F E r) = cmpS F P.asIdeal (Ideal.Quotient.mk P.asIdeal r)` using `by first`. Consider the case `rfl`. Consider the case `simp [cmpS, idS, Ideal.quotientMap_mk]`. Rewrite using `[e]`.

Use `show (RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm (Ideal.Quotient.mk (idS F P.asIdeal) (oToS F E r)) = _`. Rewrite using `[h2, RingEquiv.symm_apply_eq]`. Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
private lemma resS_alg_lemma_2 (P : Pl E) (r : 𝓞 E) {x : E ⊗[F] Formalism.L2.Herm.Af F}
    (hx : x ∈ Formalism.L2.Herm.intAf F E) (hxr : x = iA F E (algebraMap (𝓞 E) E r)) :
    resS F P ⟨x, hx⟩ = Ideal.Quotient.mk P.asIdeal r := by
  have e : (⟨x, hx⟩ : Formalism.L2.Herm.intAf F E) = oToS F E r := Subtype.ext hxr
  have h2 : Ideal.Quotient.mk (idS F P.asIdeal) (oToS F E r) =
      cmpS F P.asIdeal (Ideal.Quotient.mk P.asIdeal r) := by
    first
    | rfl
    | simp [cmpS, idS, Ideal.quotientMap_mk]
  rw [e]
  show (RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm
      (Ideal.Quotient.mk (idS F P.asIdeal) (oToS F E r)) = _
  rw [h2, RingEquiv.symm_apply_eq]
  first
  | rfl
  | simp

/- English proof (translation)
Take `⟨r, s, hs, hsa⟩` from `h`. Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Establish `hm0 : iA F E (algebraMap (𝓞 E) E s) * iA F E a ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[← map_mul, hsa]`. Conclude with `(oToS F E r).2`.

Establish `hex : ∃ c : kP P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E s) * iA F E a ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩`. Use `⟨redP P a, s, hs, hm0, ?_⟩` and prove the remaining obligations. Rewrite using `[resS_alg_lemma_2 P r hm0 (by rw [← map_mul, hsa])]`. Conclude with `mk_mul_reduction_eq_mk P hs hsa`. Unfold `redA`.

Rewrite using `[dif_pos hex]`. Take `⟨s', hs', hm', hc'⟩` from `hex.choose_spec`. Take `⟨r'', hr''⟩` from `til_tmv_int_of_iA (F := F) (a := algebraMap (𝓞 E) E s' * a) (by`. Rewrite using `[map_mul]`. Conclude with `hm')`.

Rewrite `hc'` using `[resS_alg_lemma_2 P r'' hm' (by rw [← map_mul, hr''])]`. Establish `h1` using `mk_mul_reduction_eq_mk P hs' hr''.symm`. Establish `hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Conclude with `mul_left_cancel₀ hs'0 (hc'.trans h1.symm)`.
-/
theorem til_tmv_redA_iA (P : Pl E) {a : E} (h : IntAt P a) : redA P (iA F E a) = redP P a := by
  classical
  obtain ⟨r, s, hs, hsa⟩ := h
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hm0 : iA F E (algebraMap (𝓞 E) E s) * iA F E a ∈ Formalism.L2.Herm.intAf F E := by
    rw [← map_mul, hsa]
    exact (oToS F E r).2
  have hex : ∃ c : kP P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∃ hm : iA F E (algebraMap (𝓞 E) E s) * iA F E a ∈ Formalism.L2.Herm.intAf F E,
      Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩ := by
    refine ⟨redP P a, s, hs, hm0, ?_⟩
    rw [resS_alg_lemma_2 P r hm0 (by rw [← map_mul, hsa])]
    exact mk_mul_reduction_eq_mk P hs hsa
  unfold redA
  rw [dif_pos hex]
  obtain ⟨s', hs', hm', hc'⟩ := hex.choose_spec
  obtain ⟨r'', hr''⟩ := til_tmv_int_of_iA (F := F) (a := algebraMap (𝓞 E) E s' * a) (by
    rw [map_mul]
    exact hm')
  rw [resS_alg_lemma_2 P r'' hm' (by rw [← map_mul, hr''])] at hc'
  have h1 := mk_mul_reduction_eq_mk P hs' hr''.symm
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_left_cancel₀ hs'0 (hc'.trans h1.symm)

/- English proof (translation)
Take `⟨r, s, hs, h⟩` from `h`. Use `haveI : w.asIdeal.IsPrime := w.isPrime`. Establish `hpiw : pi ∉ w.asIdeal`. Introduce `hp`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hp hpi))`.

Establish `hpi0 : algebraMap (𝓞 E) E pi ≠ 0`. Introduce `h0`. Apply `hpiw` to reduce the goal to its premises. Rewrite using `[IsFractionRing.injective (𝓞 E) E (h0.trans (map_zero _).symm)]`. Conclude with `zero_mem _`.

Establish `hspi : s * pi ∉ w.asIdeal` using `fun hm => (w.isPrime.mem_or_mem hm).elim hs hpiw`. Establish `hk : algebraMap (𝓞 E) E pi * (a / algebraMap (𝓞 E) E pi) = a`. Clear the denominators using the available nonvanishing facts. Establish `e2 : algebraMap (𝓞 E) E (s * pi) * (a / algebraMap (𝓞 E) E pi) = algebraMap (𝓞 E) E r`. Rewrite using `[map_mul, mul_assoc, hk, h]`.

Establish `h1` using `mk_mul_reduction_eq_mk w hspi e2`. Establish `h2` using `mk_mul_reduction_eq_mk w hs h`. Establish `hmpi : Ideal.Quotient.mk w.asIdeal pi = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq]`. Conclude with `hpi`.

Rewrite `h1` using `[map_mul, hmpi, mul_one]`. Establish `hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Conclude with `mul_left_cancel₀ hs0 (h1.trans h2.symm)`.
-/
theorem reduction_div_of_sub_one_mem (w : Pl E) {pi : 𝓞 E} (hpi : pi - 1 ∈ w.asIdeal) {a : E} (h : IntAt w a) :
    redP w (a / algebraMap (𝓞 E) E pi) = redP w a := by
  obtain ⟨r, s, hs, h⟩ := h
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hpiw : pi ∉ w.asIdeal := by
    intro hp
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hp hpi))
  have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro h0
    apply hpiw
    rw [IsFractionRing.injective (𝓞 E) E (h0.trans (map_zero _).symm)]
    exact zero_mem _
  have hspi : s * pi ∉ w.asIdeal := fun hm => (w.isPrime.mem_or_mem hm).elim hs hpiw
  have hk : algebraMap (𝓞 E) E pi * (a / algebraMap (𝓞 E) E pi) = a := by
    field_simp
  have e2 : algebraMap (𝓞 E) E (s * pi) * (a / algebraMap (𝓞 E) E pi) = algebraMap (𝓞 E) E r := by
    rw [map_mul, mul_assoc, hk, h]
  have h1 := mk_mul_reduction_eq_mk w hspi e2
  have h2 := mk_mul_reduction_eq_mk w hs h
  have hmpi : Ideal.Quotient.mk w.asIdeal pi = 1 := by
    rw [← map_one (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq]
    exact hpi
  rw [map_mul, hmpi, mul_one] at h1
  have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_left_cancel₀ hs0 (h1.trans h2.symm)

variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Establish `hv' : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ tilN N` using `hv`. Take `⟨s, hs, hsv⟩` from `hv'`. Rewrite `hsv` using `[mem_tilN_lemma_4]`. Take `⟨h1, r, hr⟩` from `hsv`. Establish `e : s • initL E m v = initL E m (s • v)`.

Use function extensionality and compare the values at `i`. Simplify using `[initL]`. Use `⟨⟨r, s, hs, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Simplify using `[Algebra.smul_def]`.

Use `show ∃ t ∈ P.asIdeal.primeCompl, t • initL E m v ∈ N`. Conclude with `⟨s, hs, e ▸ h1⟩`.
-/
private lemma loc_tilN_lemma_5 {m : ℕ} (P : Pl E) (N : Submodule (𝓞 E) (Sp E m)) {v : Sp E (m + 1)}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (tilN N)) :
    IntAt P (v (Fin.last m)) ∧ initL E m v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  have hv' : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ tilN N := hv
  obtain ⟨s, hs, hsv⟩ := hv'
  rw [mem_tilN_lemma_4] at hsv
  obtain ⟨h1, r, hr⟩ := hsv
  have e : s • initL E m v = initL E m (s • v) := by
    funext i
    simp [initL]
  refine ⟨⟨r, s, hs, ?_⟩, ?_⟩
  · rw [hr]
    simp [Algebra.smul_def]
  · show ∃ t ∈ P.asIdeal.primeCompl, t • initL E m v ∈ N
    exact ⟨s, hs, e ▸ h1⟩

/- English proof (translation)
Take `⟨r, s, hs, h⟩` from `ha`. Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Establish `h1` using `mk_mul_reduction_eq_mk P hs h`. Establish `h2` using `mk_mul_reduction_eq_mk P (x := algebraMap (𝓞 E) E b * a) (r := b * r) hs (by rw [map_mul, ← h]; ring)`. Establish `hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Apply `mul_left_cancel₀ hs0` to reduce the goal to its premises. Rewrite using `[h2, mul_left_comm, h1, map_mul]`.
-/
private lemma reduction_mul_of_integral' (P : Pl E) (b : 𝓞 E) {a : E} (ha : IntAt P a) :
    redP P (algebraMap (𝓞 E) E b * a) = Ideal.Quotient.mk P.asIdeal b * redP P a := by
  obtain ⟨r, s, hs, h⟩ := ha
  haveI : P.asIdeal.IsPrime := P.isPrime
  have h1 := mk_mul_reduction_eq_mk P hs h
  have h2 := mk_mul_reduction_eq_mk P (x := algebraMap (𝓞 E) E b * a) (r := b * r) hs (by rw [map_mul, ← h]; ring)
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [h2, mul_left_comm, h1, map_mul]

/- English proof (translation)
Rewrite using `[hStd]`. Simplify using `only [LinearMap.mk₂'ₛₗ_apply]`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[z0, eLast, Fin.castSucc_ne_last]`.
-/
private lemma hermStd_lastVector_apply_lemma_7 {m : ℕ} (p : E) (v : Sp E (m + 1)) :
    hStd E (m + 1) (z0 E m p) v = star p * v (Fin.last m) := by
  rw [hStd]
  simp only [LinearMap.mk₂'ₛₗ_apply]
  rw [Fin.sum_univ_castSucc]
  simp [z0, eLast, Fin.castSucc_ne_last]

/- English proof (translation)
Establish `hN` using `til_tmv_globLat (F := F) y`. Establish `hlast` using `til_tmv_lastIdx n`. Establish `hc : algebraMap (𝓞 E) E (cO E pi) = star (algebraMap (𝓞 E) E pi)` using `by first`. Consider the case `rfl`. Consider the case `simp [cO]`.

Use `Deco.ext ?_ ?_ ?_` and prove the remaining obligations. Conclude with `hN`. Use function extensionality and compare the values at `P v dsimp only [Deco.dia, Deco.til, decoRaw]`. Rewrite using `[hN]`. Use `split_ifs with hv`.

Take `⟨hint, -⟩` from `loc_tilN_lemma_5 P.1 _ hv`. Establish `hz` using `hermStd_lastVector_apply_lemma_7 (algebraMap (𝓞 E) E pi) v`. Rewrite using `[hlast, til_tmv_pullV]`. Simplify using `only [Fin.snoc_last]`. Rewrite using `[til_tmv_redA_iA P.1 hint, hcP P, hz, ← hc, reduction_mul_of_integral' P.1 _ hint]`.

Apply the tactic sequence `all_goals simp`. Use function extensionality and compare the values at `w v dsimp only [Deco.dia, Deco.til, decoRaw]`. Rewrite using `[hN]`. Use `split_ifs with hv h2`. Take `⟨hint, -⟩` from `loc_tilN_lemma_5 w.1 _ hv`.

Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[til_tmv_pullV]`. Simplify using `only [Fin.snoc_last]`. Rewrite using `[til_tmv_redA_iA w.1 hint, reduction_div_of_sub_one_mem w.1 (hw w) hint]`.

Rewrite using `[til_tmv_pullV]`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `absurd (loc_tilN_lemma_5 w.1 _ hv).2 h2`. Apply the tactic sequence `all_goals rfl`.
-/
theorem til_tmv_decoRaw (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {pi : 𝓞 E} (c : DiaG E ST)
    (hcP : ∀ P : ST, ((c P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO E pi))
    (hw : ∀ w : SG, pi - 1 ∈ w.1.asIdeal) :
    (decoRaw ST SG (padA F E n y)).dia c = (decoRaw (∅ : Finset (Pl E)) SG y).til (ST := ST) pi := by
  classical
  have hN := til_tmv_globLat (F := F) y
  have hlast := til_tmv_lastIdx n
  have hc : algebraMap (𝓞 E) E (cO E pi) = star (algebraMap (𝓞 E) E pi) := by
    first
    | rfl
    | simp [cO]
  refine Deco.ext ?_ ?_ ?_
  · exact hN
  · funext P v
    dsimp only [Deco.dia, Deco.til, decoRaw]
    rw [hN]
    split_ifs with hv
    · obtain ⟨hint, -⟩ := loc_tilN_lemma_5 P.1 _ hv
      have hz := hermStd_lastVector_apply_lemma_7 (algebraMap (𝓞 E) E pi) v
      rw [hlast, til_tmv_pullV]
      simp only [Fin.snoc_last]
      rw [til_tmv_redA_iA P.1 hint, hcP P, hz, ← hc, reduction_mul_of_integral' P.1 _ hint]
    all_goals simp
  · funext w v
    dsimp only [Deco.dia, Deco.til, decoRaw]
    rw [hN]
    split_ifs with hv h2
    · obtain ⟨hint, -⟩ := loc_tilN_lemma_5 w.1 _ hv
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [til_tmv_pullV]
        simp only [Fin.snoc_last]
        rw [til_tmv_redA_iA w.1 hint, reduction_div_of_sub_one_mem w.1 (hw w) hint]
      · rw [til_tmv_pullV]
        simp only [Fin.snoc_castSucc]
    · exact absurd (loc_tilN_lemma_5 w.1 _ hv).2 h2
    all_goals rfl

/- English proof (translation)
Establish `hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal`. Introduce `P hm`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hm` as an intermediate fact. Rewrite `this` using `[← hcP P]`. Conclude with `(c P).ne_zero this`.

Establish `hG : ∀ w : SG, pi ∉ w.1.asIdeal`. Introduce `w hm`. Establish `h1 : (1 : 𝓞 E) ∈ w.1.asIdeal`. Use `Ideal.sub_mem _ hm (hw w)` as an intermediate fact. Simplify using `using this`.

Conclude with `one_notMem w.1 h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[DecoSet.til_val _ hT hG, rlc_decoOf_val hc n ∅ SG hy]`. Use `show (decoOf ST SG (padA F E n y)).1.dia c = _`. Rewrite using `[rlc_decoOf_val hc (n + 1) ST SG (padA_mem_UAd hc hy)]`.

Conclude with `til_tmv_decoRaw ST SG y c hcP hw`.
-/
theorem til_tmv_decoOfD (hc : CMData F E) {y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hy : y ∈ UAd hc n) {pi : 𝓞 E} (c : DiaG E ST)
    (hcP : ∀ P : ST, ((c P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO E pi))
    (hw : ∀ w : SG, pi - 1 ∈ w.1.asIdeal) :
    decoOfD (n + 1) ST SG c (padA F E n y) = DecoSet.til (ST := ST) pi (decoOf (∅ : Finset (Pl E)) SG y) := by
  have hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal := by
    intro P hm
    have := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [← hcP P] at this
    exact (c P).ne_zero this
  have hG : ∀ w : SG, pi ∉ w.1.asIdeal := by
    intro w hm
    have h1 : (1 : 𝓞 E) ∈ w.1.asIdeal := by
      have := Ideal.sub_mem _ hm (hw w)
      simpa using this
    exact one_notMem w.1 h1
  apply Subtype.ext
  rw [DecoSet.til_val _ hT hG, rlc_decoOf_val hc n ∅ SG hy]
  show (decoOf ST SG (padA F E n y)).1.dia c = _
  rw [rlc_decoOf_val hc (n + 1) ST SG (padA_mem_UAd hc hy)]
  exact til_tmv_decoRaw ST SG y c hcP hw

end Ad

end Formalism.L2.Col

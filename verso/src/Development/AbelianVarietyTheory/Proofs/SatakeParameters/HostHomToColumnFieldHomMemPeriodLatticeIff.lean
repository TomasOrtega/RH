import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SeamPer

section Gen

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E') {a b : ℕ}

def trHom (x : HomE E a b) : HomE E' a b := Matrix.toLin' ((LinearMap.toMatrix' x).map e)

/- English proof (translation)
Use function extensionality and compare the values at `l`. Establish `h` using `RingHom.map_mulVec (e : E →+* E') (LinearMap.toMatrix' x) (fun k => e.symm (w k)) l`. Rewrite `h` using `[LinearMap.toMatrix'_mulVec]`. Establish `h2 : ((e : E →+* E') ∘ fun k => e.symm (w k)) = w`. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Rewrite `h` using `[h2]`. Conclude with `h.symm`.
-/
theorem trHom_apply (x : HomE E a b) (w : Sp E' a) :
    trHom e x w = fun l => e (x (fun k => e.symm (w k)) l) := by
  funext l
  have h := RingHom.map_mulVec (e : E →+* E') (LinearMap.toMatrix' x) (fun k => e.symm (w k)) l
  rw [LinearMap.toMatrix'_mulVec] at h
  have h2 : ((e : E →+* E') ∘ fun k => e.symm (w k)) = w := by
    funext k
    simp
  rw [h2] at h
  exact h.symm

/- English proof (translation)
Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `[trHom_apply]`.
-/
theorem trHom_trHom_symm (x : HomE E' a b) : trHom e (trHom e.symm x) = x := by
  refine LinearMap.ext fun w => ?_
  simp [trHom_apply]

/- English proof (translation)
Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[trHom_apply]`.
-/
theorem trHom_add (x y : HomE E a b) : trHom e (x + y) = trHom e x + trHom e y := by
  refine LinearMap.ext fun w => ?_
  funext l
  simp [trHom_apply]

/- English proof (translation)
Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[trHom_apply]`.
-/
theorem trHom_smul (r : E) (x : HomE E a b) : trHom e (r • x) = e r • trHom e x := by
  refine LinearMap.ext fun w => ?_
  funext l
  simp [trHom_apply]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨r, hr, y, hy, rfl⟩` from `hz`. Use `Submodule.subset_span ⟨e r, hA r hr, trHom e y, ?_, trHom_smul e r y⟩` and prove the remaining obligations. Introduce `w hw`.

Rewrite using `[trHom_apply]`. Conclude with `hN' _ (hy _ (hN w hw))`. Consider the case `zero`. Establish `h` using `trHom_smul e 0 (0 : HomE E a b)`. Rewrite `h` using `[zero_smul, map_zero, zero_smul]`.

Rewrite using `[h]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`. Rewrite using `[trHom_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul r y _ hy`. Establish `h : trHom e (r • y) = RingOfIntegers.mapRingEquiv e r • trHom e y` using `trHom_smul e (r : E) y`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem trHom_mem {A : Submodule (𝓞 E) E} {A' : Submodule (𝓞 E') E'}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {M : Submodule (𝓞 E') (Sp E' a)} {M' : Submodule (𝓞 E') (Sp E' b)}
    (hA : ∀ r ∈ A, e r ∈ A') (hN : ∀ w ∈ M, (fun k => e.symm (w k)) ∈ N) (hN' : ∀ w ∈ N', (fun k => e (w k)) ∈ M')
    {x : HomE E a b} (hx : x ∈ perO A N N') : trHom e x ∈ perO A' M M' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨e r, hA r hr, trHom e y, ?_, trHom_smul e r y⟩
    intro w hw
    rw [trHom_apply]
    exact hN' _ (hy _ (hN w hw))
  | zero =>
    have h := trHom_smul e 0 (0 : HomE E a b)
    rw [zero_smul, map_zero, zero_smul] at h
    rw [h]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [trHom_add]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    have h : trHom e (r • y) = RingOfIntegers.mapRingEquiv e r • trHom e y := trHom_smul e (r : E) y
    rw [h]
    exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Introduce `r hr`. Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem z hz => exact h z hz`. Consider the case `zero => rw [map_zero]`. Conclude with `A'.zero_mem`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `A'.add_mem hy hz`. Consider the case `smul c y _ hy`. Establish `h1 : e (c • y) = RingOfIntegers.mapRingEquiv e c • e y` using `map_mul e (c : E) y`. Rewrite using `[h1]`.

Conclude with `A'.smul_mem _ hy`.
-/
theorem map_mem_of_span {S : Set E} {A' : Submodule (𝓞 E') E'} (h : ∀ r ∈ S, e r ∈ A') :
    ∀ r ∈ Submodule.span (𝓞 E) S, e r ∈ A' := by
  intro r hr
  induction hr using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => rw [map_zero]; exact A'.zero_mem
  | add y z _ _ hy hz => rw [map_add]; exact A'.add_mem hy hz
  | smul c y _ hy =>
    have h1 : e (c • y) = RingOfIntegers.mapRingEquiv e c • e y := map_mul e (c : E) y
    rw [h1]
    exact A'.smul_mem _ hy

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz => exact h z hz`. Consider the case `zero`. Establish `h1 : (fun k => e ((0 : Sp E a) k)) = 0` using `by funext k; simp`.

Rewrite using `[h1]`. Conclude with `M.zero_mem`. Consider the case `add y z _ _ hy hz`. Establish `h1 : (fun k => e ((y + z) k)) = (fun k => e (y k)) + fun k => e (z k)` using `by funext k; simp`. Rewrite using `[h1]`.

Conclude with `M.add_mem hy hz`. Consider the case `smul c y _ hy`. Establish `h1 : (fun k => e ((c • y) k)) = RingOfIntegers.mapRingEquiv e c • fun k => e (y k)`. Use function extensionality and compare the values at `k`. Conclude with `map_mul e (c : E) (y k)`.

Rewrite using `[h1]`. Conclude with `M.smul_mem _ hy`.
-/
theorem vec_mem_of_span {S : Set (Sp E a)} {M : Submodule (𝓞 E') (Sp E' a)} (h : ∀ w ∈ S, (fun k => e (w k)) ∈ M) :
    ∀ w ∈ Submodule.span (𝓞 E) S, (fun k => e (w k)) ∈ M := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero =>
    have h1 : (fun k => e ((0 : Sp E a) k)) = 0 := by funext k; simp
    rw [h1]; exact M.zero_mem
  | add y z _ _ hy hz =>
    have h1 : (fun k => e ((y + z) k)) = (fun k => e (y k)) + fun k => e (z k) := by funext k; simp
    rw [h1]; exact M.add_mem hy hz
  | smul c y _ hy =>
    have h1 : (fun k => e ((c • y) k)) = RingOfIntegers.mapRingEquiv e c • fun k => e (y k) := by
      funext k
      exact map_mul e (c : E) (y k)
    rw [h1]
    exact M.smul_mem _ hy

end Gen

/- English proof (translation)
Use `vec_mem_of_span s.iE.symm ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `using hy`.
-/
theorem symm_mem_of_mem_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    ∀ w ∈ s.lat N, (fun k => s.iE.symm (w k)) ∈ N := by
  refine vec_mem_of_span s.iE.symm ?_
  rintro _ ⟨y, hy, rfl⟩
  simpa using hy

/- English proof (translation)
Introduce `w hw` and use `Submodule.subset_span (Set.mem_image_of_mem (fun x i => s.iE (x i)) hw)`.
-/
theorem vec_mem_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    ∀ w ∈ N, (fun k => s.iE (w k)) ∈ s.lat N :=
  fun w hw => Submodule.subset_span (Set.mem_image_of_mem (fun x i => s.iE (x i)) hw)

/- English proof (translation)
Introduce `D X s _ cc δ B χ cD a b _ _ N N' x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite using `[← trHom_trHom_symm s.iE x]`. Use `trHom_mem s.iE ?_ (symm_mem_of_mem_lat s N) (vec_mem_lat s N') hx` and prove the remaining obligations.

Use `map_mem_of_span s.iE ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, t, ht, rfl⟩`. Conclude with `Submodule.subset_span ⟨c, hc, t, ht, s.iE.apply_symm_apply _⟩`. Introduce `hx`. Use `trHom_mem s.iE.symm ?_ (vec_mem_lat s N) (symm_mem_of_mem_lat s N') hx` and prove the remaining obligations.

Use `map_mem_of_span s.iE.symm ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, t, ht, rfl⟩`. Conclude with `Submodule.subset_span ⟨c, hc, t, ht, rfl⟩`.
-/
theorem seamHom_mem_perO : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), ∀ x : HomE D.host.E a b, seamHom s x ∈ perO (ambOf s B χ cD).AA N N' ↔ x ∈ perO (aaOf D cc) (s.lat N) (s.lat N') := by
  intro D X s _ cc δ B χ cD a b _ _ N N' x
  constructor
  · intro hx
    rw [← trHom_trHom_symm s.iE x]
    refine trHom_mem s.iE ?_ (symm_mem_of_mem_lat s N) (vec_mem_lat s N') hx
    refine map_mem_of_span s.iE ?_
    rintro _ ⟨c, hc, t, ht, rfl⟩
    exact Submodule.subset_span ⟨c, hc, t, ht, s.iE.apply_symm_apply _⟩
  · intro hx
    refine trHom_mem s.iE.symm ?_ (vec_mem_lat s N) (symm_mem_of_mem_lat s N') hx
    refine map_mem_of_span s.iE.symm ?_
    rintro _ ⟨c, hc, t, ht, rfl⟩
    exact Submodule.subset_span ⟨c, hc, t, ht, rfl⟩

end GlobalTheory.TwV.SeamPer

end

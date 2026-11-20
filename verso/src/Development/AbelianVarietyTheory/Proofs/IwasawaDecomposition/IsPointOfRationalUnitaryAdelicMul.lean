import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}

omit [NumberField E] [StarRing E] in

/- English proof (translation)
Simplify using `[Formalism.UG.glEquiv]`.
-/
theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

/- English proof (translation)
Establish `hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ` using `(ratEquiv hc n).apply_symm_apply γ`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ`.

Simplify using `only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1`. Rewrite using `[← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]`. Use `show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _`. Rewrite using `[glEquiv_toGLm]`.
-/
theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]

omit [NumberField E] [StarRing E] in

/- English proof (translation)
Rewrite using `[LinearEquiv.symm_apply_eq]`. Simplify using `[Formalism.UG.glEquiv, Matrix.mulVec_mulVec]`.
-/
theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

/- English proof (translation)
Establish `h` using `Formalism.L2.Col.pullV_rawSm γ g 1 x`. Rewrite `h` using `[inv_one, mul_one, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[glEquiv_symm_apply]`. Conclude with `h`.
-/
theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Establish `hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N`. Rewrite using `[← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]`. Use extensionality with `w`. Use `(h.lat _).symm.trans ?_` and prove the remaining obligations. Use `show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N`.

Rewrite using `[inv_one, Units.val_one, Matrix.one_mulVec]`. Establish `hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈ Formalism.UG.stabGL (Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by`. Rewrite using `[inv_one]`. Conclude with `one_mem _`. Establish `hN2` using `Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst`.

Rewrite `hN2` using `[inv_one, mul_one]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (ratIn hc n γ).2 h.uni`. Establish `hc2` using `PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)`. Rewrite `hc2` using `[hN2, hN]`.

Conclude with `hc2`. Introduce `P x hx i hi`. Establish `hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N` using `(mem_gmap _ _ _).1 hx`. Rewrite using `[pullV_ratMul]`. Conclude with `h.f P _ hx' i hi`.

Introduce `w x hx i`. Establish `hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N` using `(mem_gmap _ _ _).1 hx`. Use `show HasRes w.1 _ (((((1 : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)`. Rewrite using `[Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]`. Conclude with `h.be w _ hx' i`.

Introduce `P i j show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)`. Establish `e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1` using `by simp`. Rewrite using `[e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[h.fr P l j]`. Use `congr 1`. Use `show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _`. Rewrite using `[adAt_inclE]`.
-/
theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp
    rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n ST SG Q γ g p h`. Establish `hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ` using `(ratEquiv hc n).apply_symm_apply γ`. Establish `hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E)` using `by show Formalism.UG.bc (iA F E) (ufGL E n γ) = _`. Rewrite using `[ufGL_eq hc]`. Use `isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h` as an intermediate fact.

Rewrite `this` using `[hγ]`. Rewrite using `[hR]`. Conclude with `this`.
-/
theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove

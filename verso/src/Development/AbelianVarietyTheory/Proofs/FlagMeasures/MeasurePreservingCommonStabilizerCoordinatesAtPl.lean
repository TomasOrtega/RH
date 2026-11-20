import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

/- English proof (translation)
Use `⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩` and prove the remaining obligations. Use `(Measure.pi_eq fun s _ => ?_).symm` and prove the remaining obligations. Establish `hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j)`. Use extensionality with `f`. Simplify using `[MeasurableEquiv.coe_curry_symm, Prod.forall]`.

Rewrite using `[MeasurableEquiv.map_apply, hpre, Measure.pi_pi]`. Repeatedly rewrite using `[Measure.pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`.
-/
private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/- English proof (translation)
Establish `h` using `MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)`. Rewrite `h` using `[MeasurableEquiv.symm_symm]`. Then use the resulting hypothesis.
-/
theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

/- English proof (translation)
Establish `h1` using `measurePreserving_curry_symm_pi ι κ A μ`. Establish `h2` using `measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)`. Establish `h3` using `curry_mp κ ι A μ`. Establish `key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) = (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘ (MeasurableEquiv.curry ι κ A).symm`. Use function extensionality and compare the values at `f v i`.

Simplify using `[MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]`. Rewrite using `[key]`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Establish `h1` using `hf.prod hg`. Establish `h2` using `MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))`. Conclude with `h2.comp h1`.
-/
theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

/- English proof (translation)
Use `show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))`. Use `infer_instance`.
-/
theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

/- English proof (translation)
Use `sigmaFinite_volume_pi_family J A` as an intermediate fact. Use `show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))`. Use `infer_instance`.
-/
theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

/- English proof (translation)
Use `sigmaFinite_volume_pi_family I A` as an intermediate fact. Conclude with `swap_mp I ι A volume`.
-/
theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

/- English proof (translation)
Introduce `ι _ k r j β`. Establish `s0` using `Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ`. Establish `s1` using `Transp.sigmaFinite_volume_pi_family (UTin β) ℂ`. Establish `s2` using `Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)`. Establish `s3` using `Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ`.

Establish `s4` using `Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ`. Establish `t1` using `Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ`. Establish `t2` using `Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)`. Establish `t3` using `Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ`. Establish `t4` using `Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ`.

Establish `p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))` using `by show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ))) infer_instance`. Establish `p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))` using `by show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) infer_instance`. Establish `q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))` using `by show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ))) infer_instance`. Establish `q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))` using `by show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) infer_instance`. Establish `e1` using `Transp.swap_vol (UTin β) ι ℂ`.

Establish `e2` using `Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)`. Establish `e3` using `Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ`. Establish `e4` using `Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ`. Establish `g` using `Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))`. Conclude with `g`.
-/
theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov

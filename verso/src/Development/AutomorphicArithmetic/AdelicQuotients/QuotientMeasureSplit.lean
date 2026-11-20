import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotProd
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotMap
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology
open scoped ENNReal

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Establish `he : Measurable e` using `(map_continuous e).measurable`. Use `⟨e.isHaarMeasure_map m, ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[Measure.inv_def, Measure.map_map measurable_inv he]`. Establish `hc : (Inv.inv ∘ e : A → B) = e ∘ Inv.inv`.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[hc, ← Measure.map_map he measurable_inv, Measure.map_inv_eq_self]`.
-/
private theorem uni_map {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [MeasurableSpace A] [BorelSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [MeasurableSpace B] [BorelSpace B] {m : Measure A} (h : Uni m) (e : A ≃ₜ* B) :
    Uni (m.map e) := by
  obtain ⟨h1, h2⟩ := h
  have he : Measurable e := (map_continuous e).measurable
  refine ⟨e.isHaarMeasure_map m, ⟨?_⟩⟩
  rw [Measure.inv_def, Measure.map_map measurable_inv he]
  have hc : (Inv.inv ∘ e : A → B) = e ∘ Inv.inv := by
    funext x
    simp
  rw [hc, ← Measure.map_map he measurable_inv, Measure.map_inv_eq_self]

/- English proof (translation)
Take `⟨ρ, -, hρ, -⟩` from `normEx R R l (MonoidHom.id R) l hP`. Take `⟨-, -, h3⟩` from `quotEq R R l (MonoidHom.id R) l hP (fun _ => 1) measurable_const (fun _ _ => rfl) _ hρ`. Rewrite using `[h3]`. Establish `h` using `hρ.2 1`. Simplify using `only [MonoidHom.id_apply, mul_one] at h`.

Simplify using `only [one_mul]`. Establish `h4 : ∫ x, (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ) ∂l = ((∫ x, (ρ x : ℝ≥0∞).toReal ∂l : ℝ) : ℂ)` using `integral_ofReal`. Rewrite using `[h4, integral_toReal hρ.1.aemeasurable (ae_of_all _ fun x => ENNReal.coe_lt_top), h]`. Simplify using the standard rewrite rules.
-/
private theorem qI_one_id {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R]
    [BorelSpace R] {l : Measure R} (hP : Pair l (MonoidHom.id R) l) :
    qI l (MonoidHom.id R) l (fun _ => 1) = 1 := by
  obtain ⟨ρ, -, hρ, -⟩ := normEx R R l (MonoidHom.id R) l hP
  obtain ⟨-, -, h3⟩ := quotEq R R l (MonoidHom.id R) l hP (fun _ => 1) measurable_const
    (fun _ _ => rfl) _ hρ
  rw [h3]
  have h := hρ.2 1
  simp only [MonoidHom.id_apply, mul_one] at h
  simp only [one_mul]
  have h4 : ∫ x, (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ) ∂l = ((∫ x, (ρ x : ℝ≥0∞).toReal ∂l : ℝ) : ℂ) :=
    integral_ofReal
  rw [h4, integral_toReal hρ.1.aemeasurable (ae_of_all _ fun x => ENNReal.coe_lt_top), h]
  simp

/- English proof (translation)
Introduce `G₁ _ _ _ _ _ _ _ _ T₁ _ _ _ _ _ _ _ _ R _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j₁ ν l hP hl e eT j hj`. Establish `hPl : Pair l (MonoidHom.id R) l` using `⟨hl, IsClosedEmbedding.id, hl⟩`. Take `⟨hPP, hQ⟩` from `quotProd_of normEx quotEq G₁ T₁ R R μ j₁ ν hP l (MonoidHom.id R) l hPl`. Establish `hje : ∀ x : T₁ × R, j (eT x) = e (j₁.prodMap (MonoidHom.id R) x)` using `fun x => hj x`. Establish `hcomp : (j : T → G) = e ∘ (j₁.prodMap (MonoidHom.id R)) ∘ eT.symm`.

Use function extensionality and compare the values at `t`. Use `hje (eT.symm t)` as an intermediate fact. Simplify using `using this`. Establish `hcl : IsClosedEmbedding j`. Rewrite using `[hcomp]`.

Conclude with `e.toHomeomorph.isClosedEmbedding.comp (hPP.2.1.comp eT.symm.toHomeomorph.isClosedEmbedding)`. Establish `hPair : Pair ((μ.prod l).map e) j ((ν.prod l).map eT)` using `⟨uni_map hPP.1 e, hcl, uni_map hPP.2.2 eT⟩`. Use `⟨hPair, fun F hF hFi => ?_⟩` and prove the remaining obligations. Establish `he : Measurable e` using `(map_continuous e).measurable`. Establish `heT : Measurable eT` using `(map_continuous eT).measurable`.

Establish `hjm : Measurable j` using `hcl.continuous.measurable`. Establish `hjp : Measurable (j₁.prodMap (MonoidHom.id R))` using `hPP.2.1.continuous.measurable`. Establish `hf : Measurable (fun x => F (e (x, (1 : R))))` using `hF.comp (he.comp (measurable_id.prodMk measurable_const))`. Establish `hfi : ∀ t g, F (e (j₁ t * g, (1 : R))) = F (e (g, (1 : R)))`. Introduce `t g`.

Establish `h : e (j₁ t * g, (1 : R)) = j (eT (t, 1)) * e (g, 1)`. Rewrite using `[hj, ← map_mul]`. Simplify using the standard rewrite rules. Rewrite using `[h, hFi]`. Establish `h1` using `(hQ (fun x => F (e (x, (1 : R)))) (fun _ => 1) hf hfi measurable_const (fun _ _ => rfl)).2`.

Rewrite `h1` using `[qI_one_id hPl, mul_one]`. Rewrite using `[← h1]`. Establish `hmap : (ν.prod l).map (fun t => e (j₁.prodMap (MonoidHom.id R) t)) = ((ν.prod l).map eT).map j`. Rewrite using `[Measure.map_map hjm heT]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Conclude with `(hje t).symm`. Establish `h2` using `(quotMap_of normEx quotEq (G₁ × R) (T₁ × R) G T (μ.prod l) (j₁.prodMap (MonoidHom.id R)) (ν.prod l) hPP ((μ.prod l).map e) j ((ν.prod l).map eT) hPair e 1 rfl hmap F hF hFi).2`. Rewrite using `[← h2]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Establish `h3 : e g = j (eT (1, g.2)) * e (g.1, 1)`. Rewrite using `[hj, ← map_mul]`. Simplify using the standard rewrite rules. Simplify using `only [mul_one]`.

Rewrite using `[h3, hFi]`.
-/
theorem UpperTheory.quotient_measure_split :
    SplitQ := by
  intro G₁ _ _ _ _ _ _ _ _ T₁ _ _ _ _ _ _ _ _ R _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _
    T _ _ _ _ _ _ _ _ μ j₁ ν l hP hl e eT j hj
  have hPl : Pair l (MonoidHom.id R) l := ⟨hl, IsClosedEmbedding.id, hl⟩
  obtain ⟨hPP, hQ⟩ := quotProd_of normEx quotEq G₁ T₁ R R μ j₁ ν hP l (MonoidHom.id R) l hPl
  have hje : ∀ x : T₁ × R, j (eT x) = e (j₁.prodMap (MonoidHom.id R) x) := fun x => hj x
  have hcomp : (j : T → G) = e ∘ (j₁.prodMap (MonoidHom.id R)) ∘ eT.symm := by
    funext t
    have := hje (eT.symm t)
    simpa using this
  have hcl : IsClosedEmbedding j := by
    rw [hcomp]
    exact e.toHomeomorph.isClosedEmbedding.comp
      (hPP.2.1.comp eT.symm.toHomeomorph.isClosedEmbedding)
  have hPair : Pair ((μ.prod l).map e) j ((ν.prod l).map eT) :=
    ⟨uni_map hPP.1 e, hcl, uni_map hPP.2.2 eT⟩
  refine ⟨hPair, fun F hF hFi => ?_⟩
  have he : Measurable e := (map_continuous e).measurable
  have heT : Measurable eT := (map_continuous eT).measurable
  have hjm : Measurable j := hcl.continuous.measurable
  have hjp : Measurable (j₁.prodMap (MonoidHom.id R)) := hPP.2.1.continuous.measurable
  have hf : Measurable (fun x => F (e (x, (1 : R)))) :=
    hF.comp (he.comp (measurable_id.prodMk measurable_const))
  have hfi : ∀ t g, F (e (j₁ t * g, (1 : R))) = F (e (g, (1 : R))) := by
    intro t g
    have h : e (j₁ t * g, (1 : R)) = j (eT (t, 1)) * e (g, 1) := by
      rw [hj, ← map_mul]
      simp
    rw [h, hFi]
  have h1 := (hQ (fun x => F (e (x, (1 : R)))) (fun _ => 1) hf hfi measurable_const
    (fun _ _ => rfl)).2
  rw [qI_one_id hPl, mul_one] at h1
  rw [← h1]
  have hmap : (ν.prod l).map (fun t => e (j₁.prodMap (MonoidHom.id R) t)) =
      ((ν.prod l).map eT).map j := by
    rw [Measure.map_map hjm heT]
    congr 1
    funext t
    exact (hje t).symm
  have h2 := (quotMap_of normEx quotEq (G₁ × R) (T₁ × R) G T (μ.prod l)
    (j₁.prodMap (MonoidHom.id R)) (ν.prod l) hPP ((μ.prod l).map e) j ((ν.prod l).map eT) hPair
    e 1 rfl hmap F hF hFi).2
  rw [← h2]
  congr 1
  funext g
  have h3 : e g = j (eT (1, g.2)) * e (g.1, 1) := by
    rw [hj, ← map_mul]
    simp
  simp only [mul_one]
  rw [h3, hFi]

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.FrameLin

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def ins (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0

def ext (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0

/- English proof (translation)
The claim follows from `L.inj h.choose_spec`.
-/
theorem choose_em (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Distinguish the cases in `h : ∃ j, L.em j = i`. Simplify using `only [ext, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]`. Establish `: i = L.i₀`. Assume the negation of the conclusion as `hi`.

Conclude with `h ((L.rng i).1 hi)`. Simplify using `only [ext, dif_neg h]`. Rewrite using `[this, hX]`.
-/
theorem ext_sub (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : ext L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [ext, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [ext, dif_neg h]
    rw [this, hX]

/- English proof (translation)
Distinguish the cases in `h : ∃ j, L.em j = k.2.1`. Simplify using `only [SD.crd, ext, ins, dif_pos h]`. Simplify using `only [SD.crd, ext, ins, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Both sides reduce to the same expression.
-/
theorem crd_ext (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (ext L X') k).2 = ins L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [SD.crd, ext, ins, dif_pos h]
  · simp only [SD.crd, ext, ins, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl

/- English proof (translation)
Use `continuous_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ j, L.em j = k.2.1`. Simplify using `only [ins, dif_pos h]`. Conclude with `continuous_apply _`. Simplify using `only [ins, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_ins : Continuous (ins L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [ins, dif_pos h]; exact continuous_apply _
  · simp only [ins, dif_neg h]; exact continuous_const

def prj (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `h : ∃ j, L.em j = L.em k.2.1` using `⟨_, rfl⟩`. Simplify using `only [prj, ins, dif_pos h, choose_em L k.2.1 h]`.
-/
theorem prj_ins (z : Fin d.m × Fin L.n × Fin 2 → Af F) : prj L (ins L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [prj, ins, dif_pos h, choose_em L k.2.1 h]

/- English proof (translation)
Use `⟨hg.1.comp_continuous (continuous_ins L), ?_⟩` and prove the remaining obligations. Establish `hc : IsCompact (prj L '' tsupport g)` using `hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)`. Use `hc.of_isClosed_subset (isClosed_tsupport _) ?_` and prove the remaining obligations. Use `(tsupport_comp_subset_preimage g (continuous_ins L)).trans fun z hz => ⟨ins L z, hz, prj_ins L z⟩` and prove the remaining obligations.
-/
theorem SB_ins {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (ins L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (continuous_ins L), ?_⟩
  have hc : IsCompact (prj L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (continuous_ins L)).trans fun z hz => ⟨ins L z, hz, prj_ins L z⟩

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [RD.loc, Matrix.map_apply, norm_star]`. Both sides reduce to the same expression.
-/
theorem sum_loc {d : SD σ} (R : RD d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [RD.loc, Matrix.map_apply, norm_star]
  rfl

/- English proof (translation)
Break down `R.hζ with h | h` into its components or cases. Conclude with `Or.inl h.2`. Conclude with `Or.inr h.2`.
-/
theorem hζ' {d : SD σ} (R : RD d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

/- English proof (translation)
It suffices to establish `key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (ext L X') a i‖ ^ 2 by`. Simplify using `only [fP, gs, key, evX, map_one]`. Rewrite using `[sum_loc, sum_loc]`. Use `Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)` and prove the remaining obligations. Establish `h : ¬ ∃ j, L.em j = i` using `fun ⟨j, hj⟩ => hi ⟨j, hj⟩`.

Establish `: (fun b => d.cw w (ext L X') b i) = 0`. Use function extensionality and compare the values at `b`. Simplify using `only [SD.cw, ext, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]`. Simplify using `[this]`. Establish `h : ∃ j', L.em j' = L.em j` using `⟨_, rfl⟩`.

Establish `e : (fun b => d.cw w (ext L X') b (L.em j)) = fun b => L.sd.cw w X' b j`. Use function extensionality and compare the values at `b`. Simplify using `only [SD.cw, ext, Matrix.map_apply, dif_pos h, choose_em L j h]`. Rewrite using `[e]`. Conclude with `norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (hζ' R') (hζ' R) (R'.hfr w) (R.hfr w) _`.
-/
theorem gauss_ext (R : RD d) (R' : RD L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (ext L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (ext L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [sum_loc, sum_loc]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (ext L X') b i) = 0 := by
      funext b
      simp only [SD.cw, ext, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (ext L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [SD.cw, ext, Matrix.map_apply, dif_pos h, choose_em L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (hζ' R')
      (hζ' R) (R'.hfr w) (R.hfr w) _

/- English proof (translation)
Use function extensionality and compare the values at `X'`. Simplify using `only [vg]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun w _ => gauss_ext L R R' w X'`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Conclude with `crd_ext L X' k`.
-/
theorem res_vg (R : RD d) (R' : RD L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => vg R g (ext L X')) = vg R' (fun z => g (ins L z)) := by
  funext X'
  simp only [vg]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => gauss_ext L R R' w X'
  · congr 1
    funext k
    exact crd_ext L X' k

def resL : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (ext L)

/- English proof (translation)
Establish `: R.vac ≤ R'.vac.comap (resL L)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `show resL L (vg R g) ∈ R'.vac`. Establish `e : resL L (vg R g) = vg R' (fun z => g (ins L z))` using `res_vg L R R' g`.

Rewrite using `[e]`. Conclude with `vg_mem R' (SB_ins L hg)`. Conclude with `this hf`.
-/
theorem res_vac (R : RD d) (R' : RD L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : resL L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (resL L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show resL L (vg R g) ∈ R'.vac
    have e : resL L (vg R g) = vg R' (fun z => g (ins L z)) := res_vg L R R' g
    rw [e]
    exact vg_mem R' (SB_ins L hg)
  exact this hf

/- English proof (translation)
Introduce `Φ hΦ hv`. Establish `h1 : resL L (d.T Φ) ∈ R'.vac` using `res_vac L R R' hv`. Establish `h2 : resL L (d.T Φ) ∈ L.sd.schM` using `(hF F E σ L.sd R').1 (vac_le_fock R' h1)`. Take `⟨Φ', hΦ', e⟩` from `(hT.1 F E σ L.sd).2.1 _ h2`. Use `⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩` and prove the remaining obligations.

Rewrite using `[e]`. Use `show d.T Φ (ext L (X.submatrix id L.em)) = d.T Φ X`. Rewrite using `[ext_sub L X hX]`.
-/
theorem vac_res' (hT : TAll) (hF : FockMem) (R : RD d) (R' : RD L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : resL L (d.T Φ) ∈ R'.vac := res_vac L R R' hv
  have h2 : resL L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (vac_le_fock R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (ext L (X.submatrix id L.em)) = d.T Φ X
  rw [ext_sub L X hX]

end PositivityTheory.SiegelWeilFormula.Avac

end

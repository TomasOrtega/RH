import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Set `S : Subalgebra ℂ (Module.End ℂ (Sm E N))` to `{ carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)} mul_mem' := fun {x y} hx hy φ hφ => by`. Take `⟨h1, e1⟩` from `hy φ hφ`. Take `⟨h2, e2⟩` from `hx _ h1`. Conclude with `⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩`. Use the proof step `add_mem' := fun {x y} hx hy φ hφ => by`.

Take `⟨h1, e1⟩` from `hx φ hφ`. Take `⟨h2, e2⟩` from `hy φ hφ`. Conclude with `⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add, e1, e2]⟩`. Use the proof step `algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ, by simp only [Module.algebraMap_end_apply, map_smul]⟩ }`. Establish `hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S` using `fun τ u φ hφ => ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩`.

Establish `hle : Zalg E N ≤ S` using `Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)`. Conclude with `hle hz`.
-/
theorem zalg_comm {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) : ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add, e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S := fun τ u φ hφ =>
    ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩
  have hle : Zalg E N ≤ S := Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)
  exact hle hz

variable {r s : ℕ}

/- English proof (translation)
Introduce `ψ hψ k g`. Establish `hAψ : IsAutForm ψ` using `hU.2 ψ hψ`. Establish `hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U` using `fun X φ hφ => hU.1 (.lie X) φ hφ`. Set `L` to `GlobalTheory.DiscClosure.stabSub ψ`. Establish `hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))` using `hAψ.level`.

Establish `hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ` using `fun h hh => by`. Establish `e` using `hT.equiv (.fin h) ψ hψ`. Establish `hh' : finRep E (r + s) h ψ = ψ` using `hh`. Express the relevant statement in the definitionally equal form `T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e`. Rewrite using `[← e, hh']`.

Set `S` to `GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)`. Establish `: FiniteDimensional ℂ S`. Use `hAψ.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨κ, rfl⟩`.

Conclude with `⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩`. Set `ρ` to `GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))`. Establish `hρ : GlobalTheory.Published.AutFin.IsContRep ρ` using `GlobalTheory.CuspRep.LocEx.isContRep_sub S _`. Establish `hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈ GlobalTheory.Published.AutFin.coeffSpan ρ` using `fun g' => GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'`. Use `hAψ.zfin` as an intermediate fact.

Set `J : Set (Module.End ℂ (Sm E (r + s)))` to `{z | z ∈ Zalg E (r + s) ∧ z ψ = 0}`. Establish `hJ : Cofin J` using `PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ`. Establish `hJZ : J ⊆ Zalg E (r + s)` using `fun z hz => hz.1`. Establish `hZ : ∀ z ∈ J, z (T ψ) = 0`. Introduce and unpack `z ⟨hz, hzψ⟩`.

Rewrite using `[← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]`. Take `⟨J₁, -, c₁, -, k₁, -⟩` from `centre J hJ`. Set `L₁` to `Slice1.levelOne s L g`. Set `ρ₁` to `ρ.comp (Slice1.levK E r s)`. Use `PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁ (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁` as an intermediate fact.

Set `S₁` to `Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)`. Establish `: FiniteDimensional ℂ S₁` using `Submodule.finiteDimensional_of_le inf_le_right`. Set `U'` to `S₁.map (Sm E r).subtype`. Take `⟨P, a, ha⟩` from `SliceTensor.interp U'`. Set `f : GA E r × GA E s → ℂ` to `fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)`.

Establish `hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U'`. Introduce `m₂`. Take `⟨ψ₁, hψA, hψ₁, -⟩` from `hT.left ψ hψ k g m₂`. Establish `hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁`. Use `SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_` and prove the remaining obligations.

Rewrite using `[hψ₁, infGL_comm, mul_assoc]`. Establish `hls : ψ₁ ∈ lsF r s (T ψ) k g` using `⟨m₂, fun m₁ => hψ₁ m₁⟩`. Conclude with `⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩`. Establish `hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ)`. Introduce `κ`.

Take `⟨b, hb, e⟩` from `(a κ).2`. Conclude with `⟨b, hb.1, e⟩`. Use `choose b hbm hbe using hb`. Establish `hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂)`. Introduce `κ`.

Take `⟨ψ₂, -, e, -⟩` from `hT.right ψ hψ k g κ.1`. Conclude with `⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩`. Use `choose q hqm hqe using hright`. Establish `hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2`. Introduce `m`.

Establish `e` using `congrFun (ha _ (hleft m.2)) m.1`. Rewrite `e` using `[Finset.sum_apply]`. Use `e.trans (Finset.sum_congr rfl fun κ _ => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, hbe, hqe]`. Expand and normalize the polynomial expressions, which then agree.

Set `eP` to `(Fintype.equivFin P).symm`. Use `⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]`. Conclude with `(Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm`.
-/
theorem expand {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) : ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ Submodule.span ℂ (lsF r s (T ψ) k g)) ∧
        (∀ i, q i ∈ rsF r s (T ψ) k g) ∧
        ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  intro ψ hψ k g
  have hAψ : IsAutForm ψ := hU.2 ψ hψ
  have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ

  let L := GlobalTheory.DiscClosure.stabSub ψ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAψ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ := fun h hh => by
    have e := hT.equiv (.fin h) ψ hψ
    have hh' : finRep E (r + s) h ψ = ψ := hh
    change T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)
  have : FiniteDimensional ℂ S := by
    have := hAψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g' =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'

  have := hAψ.zfin
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z ψ = 0}
  have hJ : Cofin J := PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ
  have hJZ : J ⊆ Zalg E (r + s) := fun z hz => hz.1
  have hZ : ∀ z ∈ J, z (T ψ) = 0 := by
    rintro z ⟨hz, hzψ⟩
    rw [← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U' := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U'
  let f : GA E r × GA E s → ℂ := fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U' := by
    intro m₂
    obtain ⟨ψ₁, hψA, hψ₁, -⟩ := hT.left ψ hψ k g m₂
    have hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_
      rw [hψ₁, infGL_comm, mul_assoc]
    have hls : ψ₁ ∈ lsF r s (T ψ) k g := ⟨m₂, fun m₁ => hψ₁ m₁⟩
    exact ⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ₂, -, e, -⟩ := hT.right ψ hψ k g κ.1
    exact ⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩
  choose q hqm hqe using hright
  have hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2 := by
    intro m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  let eP := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩
  rw [show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]
  exact (Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
